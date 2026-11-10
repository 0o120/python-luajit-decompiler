# Try the examples

The repository includes a small, original Lua source. To compile it, you need
LuaJIT on `PATH`. Run these commands from the repository root:

```sh
luajit -bs examples/basic.lua examples/basic.luac
python luajit-decompiler.py examples/basic.luac -o output -m -f
```

Open `output/basic.lua`. Function behavior and values are reconstructed, while
local names may differ because `-bs` strips debug information. To preserve debug
information in the input, compile with `-bg` instead:

```sh
luajit -bg examples/basic.lua examples/basic.luac
python luajit-decompiler.py examples/basic.luac -o output -m -f
```

Generated `.luac` files and the `output` directory are ignored by Git.
LuaJIT is not needed when decompiling bytecode you already have.

## Table decompression

`tables.lua` demonstrates rows that share default values through a metatable:

```sh
luajit -bs examples/tables.lua examples/tables.luac
python luajit-decompiler.py examples/tables.luac -o output -m -f --decompress-tables
```

Inspect `output/tables.lua` to see the expanded row fields. Replace
`--decompress-tables` with `--decompress-tables-aggressive` to also remove
recognized scaffolding that becomes unused.
