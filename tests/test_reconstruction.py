"""Regression checks for condition reconstruction and return values.

Run with ``python -m unittest discover -s tests -v``.
Runtime checks require LuaJIT on PATH (or the LUAJIT environment variable).
LUAJIT_DECOMPILER can select an older script for before/after comparisons.
"""
from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


DECOMPILER = Path(os.environ.get(
    "LUAJIT_DECOMPILER", Path(__file__).resolve().parents[1] / "luajit-decompiler.py"
)).resolve()
LUAJIT = os.environ.get("LUAJIT") or shutil.which("luajit")
spec = importlib.util.spec_from_file_location("reconstruction_decompiler", DECOMPILER)
decompiler = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = decompiler
spec.loader.exec_module(decompiler)


def new_ast():
    return decompiler.Ast(
        decompiler.Bytecode("regression.luac"), False, True,
        decompiler.DEFAULT_FORMAT_ARG, decompiler.DEFAULT_FORMAT_LABEL,
        decompiler.DEFAULT_FORMAT_ITER, decompiler.DEFAULT_FORMAT_VAR,
    )


class ReturnRegressionTests(unittest.TestCase):
    def test_ret1_always_returns_exactly_one_slot(self):
        for operand in (0, 1, 2, 7):
            with self.subTest(operand=operand):
                ast = new_ast()
                statement = ast.new_statement(decompiler.AST_STATEMENT.AST_STATEMENT_RETURN)
                statement.instruction.type = decompiler.BC_OP.BC_OP_RET1
                statement.instruction.a = 3
                statement.instruction.d = operand
                # RET1 does not consult the containing function or the D operand.
                ast.build_expressions(None, [statement])
                self.assertEqual(len(statement.assignment.expressions), 1)
                self.assertEqual(statement.assignment.expressions[0].variable.slot, 3)
                self.assertIsNone(statement.assignment.multres_return)

    def test_regular_and_multres_return_counts_are_preserved(self):
        for opcode, operand, expected_count, multres_slot in (
            (decompiler.BC_OP.BC_OP_RET, 4, 3, None),
            (decompiler.BC_OP.BC_OP_RETM, 2, 2, 5),
            (decompiler.BC_OP.BC_OP_RET0, 1, 0, None),
        ):
            with self.subTest(opcode=opcode):
                ast = new_ast()
                statement = ast.new_statement(decompiler.AST_STATEMENT.AST_STATEMENT_RETURN)
                statement.instruction.type = opcode
                statement.instruction.a = 3
                statement.instruction.d = operand
                ast.build_expressions(None, [statement])
                self.assertEqual(len(statement.assignment.expressions), expected_count)
                actual_multres = statement.assignment.multres_return
                self.assertEqual(
                    actual_multres.variable.slot if actual_multres else None, multres_slot
                )


# Include nil, false, and truthy non-booleans: boolean-only tests miss Lua's
# value-preserving and/or semantics. The trace also checks evaluation order.
RUNNER = r'''
local fn = assert(loadfile(arg[1]))()
local values = {false, 0, 1, "", "value"}
local trace = {}
function probe(value, tag)
    trace[#trace + 1] = tag
    return value
end
local function capture(...)
    local result = {}
    for i = 1, select("#", ...) do
        local value = select(i, ...)
        result[#result + 1] = type(value) .. ":" .. tostring(value)
    end
    return table.concat(result, "|")
end
for i = 1, 6 do
    for j = 1, 6 do
        for k = 1, 6 do
            trace = {}
            local result = capture(fn(values[i], values[j], values[k]))
            print(i, j, k, result, table.concat(trace, ","))
        end
    end
end
'''

CASES = {
    "and_or_values": "return a and b or c",
    "nested_values": "return (a or b) and (b or c) or a",
    "boolean_values": "return (a and not b) or (c and a)",
    "boolean_coercion": "return not (a and b), not (a or c), not not (b or c)",
    "assignment_target": "local value = a; value = b and value or c; return value",
    "alternate_targets": (
        "local value = a; value = (b and value) or (c and value) or b; return value"
    ),
    "nested_assignment": "local value = (a or b) and (not b or c); return value",
    "assignment_with_empty_fallback": (
        "local value = a; "
        "if b == 0 then value = 1 elseif b == 1 then value = 3 "
        "elseif b == false then value = 5 elseif b == nil then end; return value"
    ),
    "boolean_assignment_with_empty_fallback": (
        "local value = c; if a == 0 then value = true elseif a == b then end; return value"
    ),
    "short_circuit_calls": (
        'return probe(a, "a") and probe(b, "b") or probe(c, "c")'
    ),
    "nested_short_circuit_calls": (
        'return (probe(a, "a") or probe(b, "b")) and probe(c, "c")'
    ),
    "if_conditions": (
        "if (a and not b) or (not a and c) then return b, c end; return a, false"
    ),
    "captured_assignment": (
        "local value; value = a or function() return value end; "
        'if type(value) == "function" then return value() == value end; return value'
    ),
    "table_index": "local t = {}; t[a or b or c or 1] = c; return t[a or b or c or 1]",
}


@unittest.skipUnless(LUAJIT, "LuaJIT is needed for runtime equivalence checks")
class RuntimeRegressionTests(unittest.TestCase):
    def run_command(self, *command):
        result = subprocess.run(command, capture_output=True, timeout=30)
        self.assertEqual(
            result.returncode, 0,
            result.stdout.decode("utf-8", errors="replace")
            + result.stderr.decode("utf-8", errors="replace"),
        )
        return result.stdout

    def test_conditions_preserve_values_and_side_effects(self):
        with tempfile.TemporaryDirectory(prefix="luajit_reconstruction_") as directory:
            root = Path(directory)
            runner = root / "runner.lua"
            runner.write_text(RUNNER, encoding="utf-8")
            for name, body in CASES.items():
                source = root / (name + ".lua")
                source.write_text(
                    "return function(a, b, c)\n" + body + "\nend\n", encoding="utf-8"
                )
                expected = self.run_command(LUAJIT, str(runner), str(source))
                for mode in ("-bs", "-bg"):
                    with self.subTest(case=name, mode=mode):
                        bytecode = root / (name + ".luac")
                        self.run_command(LUAJIT, mode, str(source), str(bytecode))
                        output_dir = root / mode.lstrip("-")
                        self.run_command(
                            sys.executable, "-B", str(DECOMPILER), str(bytecode),
                            "-o", str(output_dir), "-f", "-m", "--fail-on-unsupported-statements",
                        )
                        output = output_dir / source.name
                        actual = self.run_command(LUAJIT, str(runner), str(output))
                        self.assertEqual(actual, expected, output.read_text(encoding="latin1"))


if __name__ == "__main__":
    unittest.main()
