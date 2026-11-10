# Python LuaJIT Decompiler

[![Tests](https://github.com/0o120/python-luajit-decompiler/actions/workflows/tests.yml/badge.svg)](https://github.com/0o120/python-luajit-decompiler/actions/workflows/tests.yml)
[![Python 3.9+](https://img.shields.io/badge/python-3.9%2B-blue)](https://www.python.org/downloads/)
[![MIT license](https://img.shields.io/badge/license-MIT-green)](LICENSE)

Turn LuaJIT bytecode into readable Lua source with a standalone Python script.
Decompile one file or a directory tree, use multiple worker processes, and
optionally expand compressed data tables. **No third-party Python packages are
required.**

## Get started

You need **Python 3.9 or newer**. LuaJIT itself is only needed to compile the
examples or run the optional runtime tests.

1. [Download the repository ZIP](https://github.com/0o120/python-luajit-decompiler/archive/refs/heads/main.zip), extract it, and open a terminal in that folder. Alternatively, clone it:

   ```sh
   git clone https://github.com/0o120/python-luajit-decompiler.git
   cd python-luajit-decompiler
   ```

2. Decompile a file, replacing `sample.luac` with your input:

   ```sh
   python luajit-decompiler.py sample.luac -o output
   ```

3. Open `output/sample.lua`.

Use `python3` in these commands if that is how your system names Python 3.
The script also works on its own: download
[luajit-decompiler.py](https://raw.githubusercontent.com/0o120/python-luajit-decompiler/main/luajit-decompiler.py)
and run it with Python. Its license notice is embedded in the file.

## Common commands

**Decompile a directory and its subdirectories:**

```sh
python luajit-decompiler.py bytecode -e .luac -o output
```

**Use 12 worker processes and replace existing output:**

```sh
python luajit-decompiler.py bytecode -e .luac -o output --workers 12 -m -f
```

`--workers` defaults to `1`; choose a count that suits your machine. `-m` uses
stable generated numbering to make comparisons easier. `-f` allows overwriting
existing output files.

**Expand recognized compressed tables:**

```sh
python luajit-decompiler.py tables.luac -o output --decompress-tables
```

**Show every option:**

```sh
python luajit-decompiler.py --help
```

Paths containing spaces need quotes. Keep the output directory outside the
input directory, especially when scanning without an extension filter.

## Features

- LuaJIT bytecode version 1 and version 2, with debug or stripped bytecode.
- Recursive directory processing with matching relative output paths.
- Multiple worker **processes** for batch decompilation.
- Optional normal or aggressive table decompression.
- Custom names for generated arguments, variables, iterators, labels, and slots.
- Debug-information controls, bytecode validation, and verbose diagnostics.
- Byte-preserving string output, including handling of malformed UTF-8.

This tool reads LuaJIT bytecode, not standard Lua bytecode. Decompiled output
cannot recover comments or names that were removed from the bytecode.
Big-endian bytecode is currently unsupported, and some reconstruction patterns
may produce `-- unsupported statement` comments. Use
`--fail-on-unsupported-statements` to reject those outputs.

## Performance

Tested on **9,685 LuaJIT files**, totaling 125,485,092 input bytes, using
CPython 3.12.0 on an AMD Ryzen 9 3900X running Windows 10.

| Worker processes | Earlier Python version | Optimized Python version | Less elapsed time |
| --- | ---: | ---: | ---: |
| 1 — one run each | 223.38 s | 206.33 s | **7.6%** |
| 12 — median of three runs each | 26.68 s | 25.05 s | **6.1%** |

All 9,685 outputs matched byte for byte. Times include process startup,
decompilation, and file writes with a warm input cache. Your results will depend
on the input files and hardware.

See [benchmark details](docs/PERFORMANCE.md) for raw timings, methodology,
validation, and commands to measure your own files.

## Documentation

- [Usage guide and complete option reference](docs/USAGE.md)
- [Benchmarks and reproduction instructions](docs/PERFORMANCE.md)
- [Examples](examples/README.md)
- [Testing and contributing](CONTRIBUTING.md)
- [Changes](CHANGELOG.md)

## Tests

```sh
python -m unittest discover -s tests -v
```

The Python-only tests run without additional software. Tests that compile and
execute Lua are enabled when `luajit` is on `PATH`, or when `LUAJIT` points to
its executable. The test suite creates its own small fixtures; no external
bytecode collection is required.

## License

MIT. Copyright and attribution notices are retained in [LICENSE](LICENSE).
