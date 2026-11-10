"""Exercise standalone execution, output protection, and worker failures."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / 'luajit-decompiler.py'
# Minimal stripped LuaJIT version-1 chunk with one RET0 instruction.
EMPTY_CHUNK = bytes([27, 76, 74, 1, 2, 11, 2, 0, 1, 0, 0, 0, 1, 71, 0, 1, 0, 0])


class CommandLineTests(unittest.TestCase):
    def run_cli(self, *args):
        return subprocess.run(
            [sys.executable, str(SCRIPT), *(str(arg) for arg in args)],
            capture_output=True, timeout=60,
        )

    def assert_success(self, result):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_help(self):
        result = self.run_cli('--help')
        self.assert_success(result)
        for flag in (b'--workers', b'--decompress-tables', b'--format-var'):
            self.assertIn(flag, result.stdout)

    def test_invalid_inputs_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            missing = self.run_cli(root / 'missing.luac', '-o', root / 'output')
            self.assertNotEqual(missing.returncode, 0)
            invalid = root / 'invalid.luac'
            invalid.write_bytes(b'not bytecode')
            result = self.run_cli(invalid, '-o', root / 'output')
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse((root / 'output/invalid.lua').exists())

    def test_directory_workers_preserve_paths_and_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inputs = root / 'input'
            (inputs / 'nested').mkdir(parents=True)
            for name in ('first.luac', 'nested/second.luac', 'nested/third.LUAC'):
                (inputs / name).write_bytes(EMPTY_CHUNK)
            (inputs / 'ignored.txt').write_text('Not bytecode', encoding='utf-8')
            for workers in (1, 2):
                self.assert_success(self.run_cli(
                    inputs, '-e', '.luac', '-o', root / str(workers),
                    '-m', '--workers', workers,
                ))
            expected_names = {'first.lua', 'nested/second.lua', 'nested/third.lua'}
            for workers in (1, 2):
                output = root / str(workers)
                self.assertEqual({path.relative_to(output).as_posix()
                                  for path in output.rglob('*.lua')}, expected_names)
            for name in expected_names:
                self.assertEqual((root / '1' / name).read_bytes(),
                                 (root / '2' / name).read_bytes())

    def test_failed_worker_returns_nonzero_and_keeps_successful_outputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inputs = root / 'input'
            inputs.mkdir()
            (inputs / 'valid.luac').write_bytes(EMPTY_CHUNK)
            (inputs / 'invalid.luac').write_bytes(b'not bytecode')
            result = self.run_cli(inputs, '-e', '.luac', '-o', root / 'output', '--workers', 2)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'failed', result.stdout.lower())
            self.assertTrue((root / 'output/valid.lua').is_file())
            self.assertFalse((root / 'output/invalid.lua').exists())

    def test_existing_output_requires_force(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'sample.luac'
            source.write_bytes(EMPTY_CHUNK)
            output = root / 'output'
            output.mkdir()
            target = output / 'sample.lua'
            target.write_bytes(b'existing output')
            refused = self.run_cli(source, '-o', output)
            self.assertNotEqual(refused.returncode, 0)
            self.assertEqual(target.read_bytes(), b'existing output')
            self.assert_success(self.run_cli(source, '-o', output, '-f'))
            self.assertNotEqual(target.read_bytes(), b'existing output')


if __name__ == '__main__':
    unittest.main()
