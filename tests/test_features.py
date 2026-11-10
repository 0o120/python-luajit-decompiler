"""Portable checks for optional output and table-decompression features."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / 'luajit-decompiler.py'
LUAJIT = os.environ.get('LUAJIT') or shutil.which('luajit')


@unittest.skipUnless(LUAJIT, 'LuaJIT is needed for feature runtime checks')
class FeatureTests(unittest.TestCase):
    def run_command(self, *args):
        result = subprocess.run([str(arg) for arg in args], capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_table_decompression_expands_rows_and_preserves_values(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = ROOT / 'examples/tables.lua'
            runner = root / 'runner.lua'
            runner.write_text('''
local rows = assert(loadfile(arg[1]))()
for i = 1, 3 do
    local row = rows[i]
    print(row.id, row.enabled, row.limit, row.label)
end
if arg[2] == "expanded" then
    assert(rawget(rows[1], "limit") == 10)
    assert(rawget(rows[1], "enabled") == true)
    assert(rawget(rows[2], "limit") == 20)
    assert(rawget(rows[3], "enabled") == false)
end
''', encoding='utf-8')
            expected = self.run_command(LUAJIT, runner, source)
            for mode in ('-bs', '-bg'):
                bytecode = root / 'tables.luac'
                self.run_command(LUAJIT, mode, source, bytecode)
                for flag in ('--decompress-tables', '--decompress-tables-aggressive'):
                    with self.subTest(mode=mode, flag=flag):
                        output = root / 'output'
                        self.run_command(sys.executable, SCRIPT, bytecode,
                                         '-o', output, '-m', '-f', flag)
                        result = output / 'tables.lua'
                        self.assertEqual(self.run_command(LUAJIT, runner, result, 'expanded'), expected)
                        if flag.endswith('aggressive'):
                            self.assertNotIn(b'setmetatable', result.read_bytes())

    def test_custom_names_and_debug_controls_preserve_results(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'functions.lua'
            source.write_text('''
return function(value)
    local total = 0
    for index = 1, value do total = total + index end
    return total, value and "ready" or "empty"
end
''', encoding='utf-8')
            runner = root / 'runner.lua'
            runner.write_text('print(assert(loadfile(arg[1]))()(5))', encoding='utf-8')
            expected = self.run_command(LUAJIT, runner, source)
            for mode in ('-bs', '-bg'):
                bytecode = root / 'functions.luac'
                self.run_command(LUAJIT, mode, source, bytecode)
                output = root / 'output'
                self.run_command(
                    sys.executable, SCRIPT, bytecode, '-o', output, '-f', '-m', '-i',
                    '--validate-bytecode', '--fail-on-unsupported-statements',
                    '--format-arg', 'argument_%s_%s', '--format-var', 'local_{0}_{1}',
                    '--format-iter', 'iteration_%s_%s', '--format-label', 'label_{0}_{1}',
                    '--format-slot', 'temporary_%s',
                )
                result = output / 'functions.lua'
                self.assertEqual(self.run_command(LUAJIT, runner, result), expected)
                self.assertIn(b'argument_', result.read_bytes())

    def test_unrestricted_byte_strings_preserve_values(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'bytes.lua'
            source.write_text(r'return "a\000b\255\128\194\160\010\034\092"', encoding='utf-8')
            bytecode = root / 'bytes.luac'
            self.run_command(LUAJIT, '-bs', source, bytecode)
            runner = root / 'runner.lua'
            runner.write_text('local s = assert(loadfile(arg[1]))(); print(s:byte(1, #s))', encoding='utf-8')
            expected = self.run_command(LUAJIT, runner, source)
            for flags in ([], ['-u']):
                with self.subTest(flags=flags):
                    output = root / 'output'
                    self.run_command(sys.executable, SCRIPT, bytecode, '-o', output, '-f', *flags)
                    self.assertEqual(self.run_command(LUAJIT, runner, output / 'bytes.lua'), expected)


if __name__ == '__main__':
    unittest.main()
