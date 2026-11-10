# Contributing

## Development setup

Clone the repository and use Python 3.9 or newer. There are no required Python
packages to install. The executable entry point is `luajit-decompiler.py`.

```sh
python luajit-decompiler.py --help
python -m unittest discover -s tests -v
```

For the runtime tests, install LuaJIT and put `luajit` on `PATH`. Alternatively,
set the `LUAJIT` environment variable to the executable's full path:

```powershell
$env:LUAJIT = "C:\tools\luajit.exe"
python -m unittest discover -s tests -v
```

Without LuaJIT, runtime-dependent tests are explicitly skipped. Python-only
tests still run. CI runs Python tests on Windows and Linux and runs the LuaJIT
runtime checks on Linux.

## Repository layout

```text
luajit-decompiler.py       Standalone decompiler, including its license notice
tests/                    Self-contained unit and runtime regressions
examples/                 Small Lua sources for trying the CLI
tools/benchmark_python.py Repeatable timing and output-verification tool
benchmarks/                Published, anonymized benchmark measurements
docs/                      Usage and performance documentation
```

## Tests and changes

Keep fixes focused. For reconstruction changes, add a small Lua example that
checks actual values, return counts, or evaluation order. Tests should create
their inputs in a temporary directory rather than depend on a private file
collection. Include both stripped and debug bytecode when relevant.

For output changes, check exact bytes, especially escapes, line endings, and
malformed UTF-8. For CLI changes, exercise the command through a subprocess.
For multiprocessing changes, compare directory output with sequential output.

The reconstruction tests accept `LUAJIT_DECOMPILER` to select a different script.
See [the benchmark guide](docs/PERFORMANCE.md) for comparing Python revisions.

## Reporting issues

Include:

- The exact command and complete error message.
- Your operating system and `python --version` output.
- Whether the file has debug information, if known.
- A small Lua source or bytecode example that reproduces the issue and that you
  are allowed to share.
- The expected result and the actual result.

Do not include credentials, local file collections, or generated dumps in a
pull request. Keep benchmark records free of personal paths and input names.

## License

Contributions are distributed under the repository's MIT license. Preserve the
existing copyright and permission notices, including the embedded notice in
the standalone script.
