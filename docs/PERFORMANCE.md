# Python benchmarks

These measurements compare two revisions of this Python decompiler: before
and after the string-output optimizations. Both use the same reconstruction
algorithms and command-line settings.

## Dataset and machine

| Item | Value |
| --- | --- |
| LuaJIT bytecode files | **9,685** |
| Total input bytes | **125,485,092** |
| CPU | AMD Ryzen 9 3900X — 12 cores, 24 logical processors |
| Operating system | Windows 10, 64-bit |
| Interpreter | CPython 3.12.0, 64-bit |
| Measurement date | November 10, 2026 |
| Common options | `-e .luac -m -f` |

## Results

| Worker processes | Earlier Python revision | Optimized Python revision | Less elapsed time |
| --- | ---: | ---: | ---: |
| 1 — one run each | 223.381 s | 206.326 s | **7.6%** |
| 12 — median of three runs each | 26.679 s | 25.051 s | **6.1%** |

Raw times for the 12-process measurements:

| Run | Earlier Python revision | Optimized Python revision |
| --- | ---: | ---: |
| 1 | 27.373 s | 25.051 s |
| 2 | 26.298 s | 25.143 s |
| 3 | 26.679 s | 24.640 s |

Full-precision timings, source hashes, and machine-readable methodology are in
[benchmarks/2026-11-10.json](../benchmarks/2026-11-10.json). The recorded source
hashes identify the revisions used for measurement, before this standalone
repository was assembled. The input collection and generated dumps are not
included in this repository.

The publication copy was subsequently rechecked against all 9,685 verified
Python outputs, with zero differences. The
[distribution validation record](../benchmarks/2026-11-10-validation.json)
identifies the checked source by SHA-256.

## What changed

- Ordinary ASCII and valid UTF-8 strings are handled in bulk instead of
  assembling the output byte by byte in Python.
- Malformed UTF-8 and C1 controls retain the established escaping rules.
- Strings are retained as whole output fragments instead of many individual
  characters.
- Formatting regexes are skipped when their required literal is absent.

The optimized output was byte-for-byte identical across all 9,685 files.
Additional validation included 159,664 string comparisons and 199 feature-output
comparisons, with 41,472 executed Lua cases. Feature checks covered custom
names, debug and stripped bytecode, unrestricted bytes, validation, legacy
bytecode, FFI values, and both table-decompression modes.

## Measurement method

Each recorded time measures the complete, unprofiled CLI process: startup,
decompilation, and file writes. The input cache was warmed before measurement.
Both revisions overwrote the same output paths, and stdout/stderr were sent to
log files. The 12-process run pairs alternated order; the one-process pair ran
the earlier revision first. No other decompiler benchmarks or test suites ran
concurrently.

After each run, all files were checked against expected output. File counts,
hashes, and refreshed timestamps were verified so that an old output could not
hide a failed worker. Verification time was excluded from the timings.

These results describe this file collection on this machine. A single-process
pair is one observation, and the parallel figures summarize three observations
per revision. Different file sizes, output destinations, cache state, and
hardware can change both throughput and the best worker count.

## Benchmark your own files

Keep a known Python revision as `baseline.py`. Prepare an input directory and
its matching expected Lua output, then run this from the repository root:

```sh
python tools/benchmark_python.py --baseline baseline.py --input bytecode --reference expected --work-dir benchmark-results --workers 12 --repeats 3
```

The current `luajit-decompiler.py` is the default candidate. To select another
Python revision, add `--candidate path/to/decompiler.py`.

The work directory **must be new**, and it must be outside the input and
reference directories. The tool prepares its own output, checks every result,
and saves logs plus `results.json`. It leaves the input and reference unchanged.
Expected relative names must match the inputs, replacing `.luac` with `.lua`.

For a single-process measurement, use another new work directory:

```sh
python tools/benchmark_python.py --baseline baseline.py --input bytecode --reference expected --work-dir benchmark-serial --workers 1 --repeats 1
```

Do not run competing benchmarks at the same time. Compare identical options,
input files, interpreter versions, and output conditions. Use more repetitions
when small timing differences matter.
