"""Byte-fidelity regressions for the optimized Lua string/output writer."""
from pathlib import Path
import importlib.util
import sys
import unittest

path = Path(__file__).resolve().parents[1] / 'luajit-decompiler.py'
spec = importlib.util.spec_from_file_location('output_optimization_decompiler', path)
decompiler = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = decompiler
spec.loader.exec_module(decompiler)


def writer(unrestricted=False):
    result = object.__new__(decompiler.Lua)
    result.write_buffer = []
    result.unrestricted_ascii = unrestricted
    return result


def render(data, unrestricted=False):
    output = writer(unrestricted)
    output.write_string(data.decode('latin1'))
    return ''.join(output.write_buffer).encode('latin1')


class StringOutputTests(unittest.TestCase):
    def test_ascii_escaping(self):
        self.assertEqual(render(b''), b'')
        self.assertEqual(render(b'plain text 123'), b'plain text 123')
        self.assertEqual(render(b'\x00\x07\x08\x09\x0a\x0b\x0c\x0d\x1f\x7f"\\'),
                         rb'\x00\a\b\t\n\v\f\r\x1F\x7F\"\\')

    def test_valid_utf8_and_escaping_can_share_a_string(self):
        data = 'é中🦀\u00a0'.encode('utf-8')
        self.assertEqual(render(data), data)
        self.assertEqual(render(b'"' + data + b'\n\\'), b'\\"' + data + b'\\n\\\\')

    def test_c1_controls_and_malformed_utf8_keep_byte_escapes(self):
        cases = {
            b'\xc2\x80':rb'\xC2\x80', b'\xc2\x9f':rb'\xC2\x9F',
            b'\xc0\xaf':rb'\xC0\xAF', b'\xed\xa0\x80':rb'\xED\xA0\x80',
            b'\xf4\x90\x80\x80':rb'\xF4\x90\x80\x80',
            b'\xe2\x82':rb'\xE2\x82', b'\x80':rb'\x80',
            b'valid\xe2\x82\xac\xff':b'valid\xe2\x82\xac\\xFF',
        }
        for data, expected in cases.items():
            with self.subTest(data=data):
                self.assertEqual(render(data), expected)

    def test_unrestricted_mode_preserves_high_bytes(self):
        self.assertEqual(render(b'\x80\xff\x7f"\\\n', True), b'\x80\xff' + rb'\x7F\"\\\n')

    def test_non_latin1_input_still_fails_before_changing_buffer(self):
        output = writer()
        output.write_buffer.append('existing')
        with self.assertRaises(UnicodeEncodeError):
            output.write_string('€')
        self.assertEqual(output.write_buffer, ['existing'])


class NormalizationTests(unittest.TestCase):
    def test_unrelated_output_is_preserved(self):
        text = 'local var_0_0 = "data"\r\n' * 10_000
        self.assertEqual(writer()._postprocess_output(text), text)

    def test_io_path_normalization_still_runs(self):
        text = ('local var_0_0 = root\r\nlocal var_0_1 = directory\r\n'
                'local var_0_2 = assert(io.open(var_0_0 .. var_0_1 .. name, "w"))\r\n\r\n'
                'var_0_3 = var_0_2\r\nvar_0_4 = var_0_2.write')
        expected = ('local var_0_0 = root .. directory .. name\r\n'
                    'local var_0_1 = assert(io.open(var_0_0, "w"))\r\n\r\n'
                    'var_0_3 = var_0_1\r\nvar_0_4 = var_0_1.write')
        self.assertEqual(writer()._postprocess_output(text), expected)

    def test_io_function_rename_still_runs(self):
        text = ('local var_0_1 = assert(io.open(var_0_0, "w"))\r\n\r\n'
                'var_0_9 = var_0_1\r\nvar_0_10 = var_0_1.write\r\n'
                'local function var_0_3()\r\n\treturn\r\nend\r\n\tvar_0_3()')
        self.assertEqual(writer()._postprocess_output(text), text.replace('var_0_3', 'var_0_2'))


if __name__ == '__main__':
    unittest.main()
