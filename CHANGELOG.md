# Changes

## Initial standalone repository — 2026-11-10

- Standalone, dependency-free Python CLI for files and directory trees.
- Multiprocessing, configurable generated names, bytecode validation, and
  optional table decompression.
- Condition, return-value, captured-variable, and string-output regressions.
- Bulk string escaping and skipped unnecessary output-normalization scans.
- Published Python benchmarks on 9,685 LuaJIT files with exact output checks.
- Portable usage documentation, examples, benchmark tooling, and CI.
- Failed multiprocessing batches return a nonzero exit status while preserving
  outputs from successful files.
