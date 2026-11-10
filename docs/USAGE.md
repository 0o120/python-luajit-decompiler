# Usage guide

## One file

```sh
python luajit-decompiler.py sample.luac -o output
```

This creates `output/sample.lua`. If `-o` is omitted, output goes into the
`output` directory beside `luajit-decompiler.py`. Existing output is protected
unless you pass `-f`.

For a path containing spaces:

```sh
python luajit-decompiler.py "input files/sample.luac" -o "decoded files"
```

The extension is only a filename convention. The file itself must contain
supported LuaJIT bytecode.

## A directory

```sh
python luajit-decompiler.py bytecode -e .luac -o decoded --workers 12 -m -f
```

The scan is recursive. For example:

```text
bytecode/
  main.luac
  modules/
    helpers.luac

decoded/
  main.lua
  modules/
    helpers.lua
```

`-e .luac` filters by extension, case-insensitively; `-e luac` also works.
Without a filter, every file in the input tree is considered. Use a separate
output directory to keep generated files out of future input scans.

`--workers` controls the number of processes. One process is the default.
More processes can speed up large collections but also use more memory. The
documented benchmark uses 12; it is not an automatic or universal optimum.

A failed batch lists its errors and returns a nonzero exit status. Successfully
decompiled files are retained so you can inspect them or retry the failures.

## Compressed tables

Some bytecode represents data rows using shared defaults and a metatable.
The optional decompression pass expands recognized patterns into explicit rows.

```sh
python luajit-decompiler.py tables.luac -o decoded --decompress-tables
```

To also remove recognized scaffolding that becomes unused:

```sh
python luajit-decompiler.py tables.luac -o decoded --decompress-tables-aggressive
```

Aggressive mode includes normal decompression; both flags are not required.
Patterns the pass does not recognize remain as reconstructed code.

## Generated names

Names stored in debug information can be retained. When names are unavailable,
the decompiler generates placeholders. `-m` makes their numbering more stable
for output comparisons. `-i` ignores debug information during reconstruction.

The generated name defaults are:

| Option | Default |
| --- | --- |
| `--format-arg` | `arg_%s_%s` |
| `--format-var` | `var_%s_%s` |
| `--format-iter` | `iter_%s_%s` |
| `--format-label` | `label_%s_%s` |
| `--format-slot` | `slot_%s` |

Two `%s` placeholders use the primary and secondary indices. A single `%s`
uses the secondary index. When `%s` is absent, Python-style formatting is
accepted: `{0}` is the primary index and `{1}` is the secondary index.

```sh
python luajit-decompiler.py sample.luac -o decoded --format-arg "argument_%s_%s" --format-var "local_{0}_{1}" --format-slot "temporary_%s"
```

Choose formats that produce valid Lua identifiers, and quote patterns as shown.

## Strings and debug output

Normal string output preserves valid UTF-8 and escapes control bytes or
malformed sequences. `-u` / `--unrestricted_ascii` emits high bytes directly;
the resulting file may not be valid UTF-8. Use it when raw-byte output is
appropriate for your data.

Use `-v` for detailed diagnostic output. For the most useful per-file trace,
run a single file with the default one worker:

```sh
python luajit-decompiler.py sample.luac -o decoded -v
```

## Complete option reference

| Option | Purpose |
| --- | --- |
| `input_path` | Required input file or directory. |
| `-h`, `--help` | Show command-line help. |
| `-o`, `--output PATH` | Output directory; defaults to `output` beside the script. |
| `-e`, `--extension EXT` | Extension filter for a directory scan. |
| `-f`, `--force_overwrite` | Replace existing output files. |
| `-w`, `--workers COUNT` | Worker processes; default `1`. |
| `-m`, `--minimize_diffs` | Stabilize generated numbering. |
| `-i`, `--ignore_debug_info` | Ignore debug information during reconstruction. |
| `-u`, `--unrestricted_ascii` | Emit high bytes directly in string literals. |
| `-v`, `--verbose` | Detailed diagnostic output. |
| `--validate-bytecode` | Parse and validate the inputs before decompilation. |
| `--fail-on-unsupported-statements` | Fail instead of writing unsupported-statement comments. |
| `--decompress-tables` | Expand recognized compressed/default table rows. |
| `--decompress-tables-aggressive` | Expand rows and remove recognized unused scaffolding. |
| `--format-arg PATTERN` | Generated argument names. |
| `--format-var PATTERN` | Generated local variable names. |
| `--format-iter PATTERN` | Generated iterator names. |
| `--format-label PATTERN` | Generated label names. |
| `--format-slot PATTERN` | Generated fallback slot names. |
| `--backend python` | Accepted compatibility option; Python is the only choice. |
| `-s`, `--silent_assertions` | Accepted compatibility option; currently has no effect. |

## Troubleshooting

| Message or symptom | What to check |
| --- | --- |
| `File already exists` | Choose a new output directory or pass `-f`. |
| `No files found` | Check the input path and extension filter. |
| `Failed to open input path` | Check spelling and quote paths containing spaces. |
| Invalid header or unsupported instruction | Confirm the input is LuaJIT bytecode. Standard Lua bytecode and customized formats may not be supported. |
| `Big endian support not implemented` | Big-endian bytecode is currently unsupported. |
| Synthetic names in output | Original names may have been stripped; try keeping debug information enabled. |
| `-- unsupported statement` in output | Retry with `--fail-on-unsupported-statements` and inspect the error. |

For a reproducible issue, include the exact command, Python version, operating
system, and a small example you can share. See [CONTRIBUTING.md](../CONTRIBUTING.md).
