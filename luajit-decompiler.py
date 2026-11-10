#!/usr/bin/env python3
"""Python LuaJIT Decompiler.

MIT License

LuaJIT Decompiler v2
Copyright (C) 2023 marsinator358

LuaJIT
Copyright (C) 2005-2023 Mike Pall. All rights reserved.

Lua
Copyright (C) 1994-2023 Lua.org, PUC-Rio.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""
from __future__ import annotations

import argparse
import builtins
import concurrent.futures
import copy
import math
import multiprocessing
import re
import struct
import sys
from dataclasses import dataclass, field
from enum import IntEnum
from pathlib import Path
from typing import Iterable, Optional


PROGRAM_NAME = "Python LuaJIT Decompiler"
DOUBLE_SIGN = 0x8000000000000000
DOUBLE_EXPONENT = 0x7FF0000000000000
DOUBLE_FRACTION = 0x000FFFFFFFFFFFFF
DOUBLE_SPECIAL = DOUBLE_EXPONENT
DOUBLE_NEGATIVE_ZERO = DOUBLE_SIGN
DEFAULT_FORMAT_ARG = "arg_%s_%s"
DEFAULT_FORMAT_LABEL = "label_%s_%s"
DEFAULT_FORMAT_ITER = "iter_%s_%s"
DEFAULT_FORMAT_VAR = "var_%s_%s"
DEFAULT_FORMAT_SLOT = "slot_%s"

# Module-level constant sets for check_valid_name (avoid re-creating per call).
_LUA_KEYWORDS = frozenset({
    "and", "break", "do", "else", "elseif", "end", "false", "for",
    "function", "if", "in", "local", "nil", "not", "or", "repeat",
    "return", "then", "true", "until", "while",
})
_INVALID_NAME_CHARS = frozenset({
    ":", ";", "<", "=", ">", "?", "@", "[", "\\", "]", "^", "`",
    "{", "|", "}", "~", "\x7F",
})

# Bulk escaping for ASCII and validated UTF-8 strings. Keep the byte-level
# writer below for malformed UTF-8 and the C1 controls it intentionally escapes.
_LUA_STRING_ESCAPES = {
    **{value: f"\\x{value:02X}" for value in range(32)},
    7: "\\a", 8: "\\b", 9: "\\t", 10: "\\n", 11: "\\v", 12: "\\f", 13: "\\r",
    34: '\\"', 92: "\\\\", 127: "\\x7F",
}
_LUA_STRING_NEEDS_ESCAPE = re.compile(rb'[\x00-\x1f\x7f"\\]')
_UTF8_C1_CONTROL = re.compile(rb'\xc2[\x80-\x9f]')


class DecompilerError(Exception):
    def __init__(
        self,
        message: str,
        file_path: str = "",
        function: str = "",
        source: str = "",
        line: int = 0,
    ) -> None:
        super().__init__(message)
        self.message = message
        self.file_path = file_path
        self.function = function
        self.source = source
        self.line = line

    def __str__(self) -> str:
        if self.function:
            return (
                f"Error running {self.function}\n"
                f"Source: {self.source}:{self.line}\n\n"
                f"File: {self.file_path}\n\n"
                f"{self.message}"
            )
        return self.message


def bitcast_u64_to_f64(value: int) -> float:
    return struct.unpack("<d", struct.pack("<Q", value & 0xFFFFFFFFFFFFFFFF))[0]


def bitcast_f64_to_u64(value: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", value))[0]


def bitcast_u32_to_i32(value: int) -> int:
    return struct.unpack("<i", struct.pack("<I", value & 0xFFFFFFFF))[0]


def bitcast_u16_to_i16(value: int) -> int:
    return struct.unpack("<h", struct.pack("<H", value & 0xFFFF))[0]


def bitcast_u64_to_i64(value: int) -> int:
    return struct.unpack("<q", struct.pack("<Q", value & 0xFFFFFFFFFFFFFFFF))[0]


def print_line(message: str) -> None:
    sys.stdout.write(f"{message}\n")
    sys.stdout.flush()


_progress_active = False
_verbose_enabled = False
_verbose_indent = 0


def set_verbose(enabled: bool) -> None:
    global _verbose_enabled, _verbose_indent, _progress_active
    _verbose_enabled = enabled
    _verbose_indent = 0
    if enabled:
        _progress_active = False


def verbose_log(message: str) -> None:
    if not _verbose_enabled:
        return
    erase_progress_bar()
    indent = "  " * _verbose_indent
    print_line(f"[verbose] {indent}{message}")


def verbose_push(message: str) -> None:
    global _verbose_indent
    verbose_log(message)
    _verbose_indent += 1


def verbose_pop(message: str = "") -> None:
    global _verbose_indent
    _verbose_indent = max(0, _verbose_indent - 1)
    if message:
        verbose_log(message)


def print_progress_bar(progress: float = 0.0, total: float = 100.0) -> None:
    global _progress_active
    if _verbose_enabled:
        return
    total = max(total, 1.0)
    threshold = int(round(20.0 / total * progress))
    threshold = max(0, min(20, threshold))
    bar = "[" + "=" * threshold + " " * (20 - threshold) + "]"
    sys.stdout.write("\r" + bar)
    sys.stdout.flush()
    _progress_active = True


def erase_progress_bar() -> None:
    global _progress_active
    if _verbose_enabled:
        _progress_active = False
        return
    if not _progress_active:
        return
    sys.stdout.write("\r" + " " * 22 + "\r")
    sys.stdout.flush()
    _progress_active = False


def byte_to_string(byte: int) -> str:
    return f"0x{byte & 0xFF:02X}"


def decompiler_assert(
    assertion: bool,
    message: str,
    file_path: str = "",
    function: str = "",
    source: str = "",
    line: int = 0,
) -> None:
    if assertion:
        return
    raise DecompilerError(message, file_path, function, source, line)


def format_generated_name(
    pattern: str,
    primary: int,
    secondary: int,
    kind: str,
    file_path: str = "",
    function: str = "",
) -> str:
    placeholder_count = pattern.count("%s")
    try:
        if placeholder_count == 1:
            return pattern % secondary
        if placeholder_count == 2:
            return pattern % (primary, secondary)
        if placeholder_count == 0:
            if "{" in pattern and "}" in pattern:
                return pattern.format(primary, secondary)
            return pattern
    except Exception as exc:
        raise DecompilerError(
            f"Invalid {kind} format '{pattern}': {exc}",
            file_path,
            function,
            __file__,
            0,
        ) from exc

    raise DecompilerError(
        (
            f"Invalid {kind} format '{pattern}': expected one or two '%s' "
            "placeholders (or Python-style '{0}'/'{1}')"
        ),
        file_path,
        function,
        __file__,
        0,
    )


BC_HEADER = b"\x1bLJ"
BC_VERSION_1 = 1
BC_VERSION_2 = 2
BC_F_BE = 0x01
BC_F_STRIP = 0x02
BC_F_FFI = 0x04
BC_F_FR2 = 0x08
BC_PROTO_CHILD = 0x01
BC_PROTO_VARARG = 0x02
BC_PROTO_FFI = 0x04
BC_UV_IMMUTABLE = 0x4000
BC_UV_LOCAL = 0x8000
BC_OP_JMP_BIAS = 0x8000


class BC_KTAB(IntEnum):
    BC_KTAB_NIL = 0
    BC_KTAB_FALSE = 1
    BC_KTAB_TRUE = 2
    BC_KTAB_INT = 3
    BC_KTAB_NUM = 4
    BC_KTAB_STR = 5


class BC_KGC(IntEnum):
    BC_KGC_CHILD = 0
    BC_KGC_TAB = 1
    BC_KGC_I64 = 2
    BC_KGC_U64 = 3
    BC_KGC_COMPLEX = 4
    BC_KGC_STR = 5


class BC_KNUM(IntEnum):
    BC_KNUM_INT = 0
    BC_KNUM_NUM = 1


class BC_VAR(IntEnum):
    BC_VAR_END = 0
    BC_VAR_FOR_IDX = 1
    BC_VAR_FOR_STOP = 2
    BC_VAR_FOR_STEP = 3
    BC_VAR_FOR_GEN = 4
    BC_VAR_FOR_STATE = 5
    BC_VAR_FOR_CTL = 6
    BC_VAR_STR = 7


class BC_OP(IntEnum):
    BC_OP_ISLT = 0
    BC_OP_ISGE = 1
    BC_OP_ISLE = 2
    BC_OP_ISGT = 3
    BC_OP_ISEQV = 4
    BC_OP_ISNEV = 5
    BC_OP_ISEQS = 6
    BC_OP_ISNES = 7
    BC_OP_ISEQN = 8
    BC_OP_ISNEN = 9
    BC_OP_ISEQP = 10
    BC_OP_ISNEP = 11
    BC_OP_ISTC = 12
    BC_OP_ISFC = 13
    BC_OP_IST = 14
    BC_OP_ISF = 15
    BC_OP_ISTYPE = 16
    BC_OP_ISNUM = 17
    BC_OP_MOV = 18
    BC_OP_NOT = 19
    BC_OP_UNM = 20
    BC_OP_LEN = 21
    BC_OP_ADDVN = 22
    BC_OP_SUBVN = 23
    BC_OP_MULVN = 24
    BC_OP_DIVVN = 25
    BC_OP_MODVN = 26
    BC_OP_ADDNV = 27
    BC_OP_SUBNV = 28
    BC_OP_MULNV = 29
    BC_OP_DIVNV = 30
    BC_OP_MODNV = 31
    BC_OP_ADDVV = 32
    BC_OP_SUBVV = 33
    BC_OP_MULVV = 34
    BC_OP_DIVVV = 35
    BC_OP_MODVV = 36
    BC_OP_POW = 37
    BC_OP_CAT = 38
    BC_OP_KSTR = 39
    BC_OP_KCDATA = 40
    BC_OP_KSHORT = 41
    BC_OP_KNUM = 42
    BC_OP_KPRI = 43
    BC_OP_KNIL = 44
    BC_OP_UGET = 45
    BC_OP_USETV = 46
    BC_OP_USETS = 47
    BC_OP_USETN = 48
    BC_OP_USETP = 49
    BC_OP_UCLO = 50
    BC_OP_FNEW = 51
    BC_OP_TNEW = 52
    BC_OP_TDUP = 53
    BC_OP_GGET = 54
    BC_OP_GSET = 55
    BC_OP_TGETV = 56
    BC_OP_TGETS = 57
    BC_OP_TGETB = 58
    BC_OP_TGETR = 59
    BC_OP_TSETV = 60
    BC_OP_TSETS = 61
    BC_OP_TSETB = 62
    BC_OP_TSETM = 63
    BC_OP_TSETR = 64
    BC_OP_CALLM = 65
    BC_OP_CALL = 66
    BC_OP_CALLMT = 67
    BC_OP_CALLT = 68
    BC_OP_ITERC = 69
    BC_OP_ITERN = 70
    BC_OP_VARG = 71
    BC_OP_ISNEXT = 72
    BC_OP_RETM = 73
    BC_OP_RET = 74
    BC_OP_RET0 = 75
    BC_OP_RET1 = 76
    BC_OP_FORI = 77
    BC_OP_JFORI = 78
    BC_OP_FORL = 79
    BC_OP_IFORL = 80
    BC_OP_JFORL = 81
    BC_OP_ITERL = 82
    BC_OP_IITERL = 83
    BC_OP_JITERL = 84
    BC_OP_LOOP = 85
    BC_OP_ILOOP = 86
    BC_OP_JLOOP = 87
    BC_OP_JMP = 88
    BC_OP_FUNCF = 89
    BC_OP_IFUNCF = 90
    BC_OP_JFUNCF = 91
    BC_OP_FUNCV = 92
    BC_OP_IFUNCV = 93
    BC_OP_JFUNCV = 94
    BC_OP_FUNCC = 95
    BC_OP_FUNCCW = 96
    BC_OP_INVALID = 97


ABC_FORMAT_OPS = {
    BC_OP.BC_OP_ADDVN,
    BC_OP.BC_OP_SUBVN,
    BC_OP.BC_OP_MULVN,
    BC_OP.BC_OP_DIVVN,
    BC_OP.BC_OP_MODVN,
    BC_OP.BC_OP_ADDNV,
    BC_OP.BC_OP_SUBNV,
    BC_OP.BC_OP_MULNV,
    BC_OP.BC_OP_DIVNV,
    BC_OP.BC_OP_MODNV,
    BC_OP.BC_OP_ADDVV,
    BC_OP.BC_OP_SUBVV,
    BC_OP.BC_OP_MULVV,
    BC_OP.BC_OP_DIVVV,
    BC_OP.BC_OP_MODVV,
    BC_OP.BC_OP_POW,
    BC_OP.BC_OP_CAT,
    BC_OP.BC_OP_TGETV,
    BC_OP.BC_OP_TGETS,
    BC_OP.BC_OP_TGETB,
    BC_OP.BC_OP_TGETR,
    BC_OP.BC_OP_TSETV,
    BC_OP.BC_OP_TSETS,
    BC_OP.BC_OP_TSETB,
    BC_OP.BC_OP_TSETR,
    BC_OP.BC_OP_CALLM,
    BC_OP.BC_OP_CALL,
    BC_OP.BC_OP_ITERC,
    BC_OP.BC_OP_ITERN,
    BC_OP.BC_OP_VARG,
}


UNSUPPORTED_OPS = {
    BC_OP.BC_OP_ISTYPE,
    BC_OP.BC_OP_ISNUM,
    BC_OP.BC_OP_TGETR,
    BC_OP.BC_OP_TSETR,
    BC_OP.BC_OP_JFORI,
    BC_OP.BC_OP_IFORL,
    BC_OP.BC_OP_JFORL,
    BC_OP.BC_OP_IITERL,
    BC_OP.BC_OP_JITERL,
    BC_OP.BC_OP_ILOOP,
    BC_OP.BC_OP_JLOOP,
    BC_OP.BC_OP_FUNCF,
    BC_OP.BC_OP_IFUNCF,
    BC_OP.BC_OP_JFUNCF,
    BC_OP.BC_OP_FUNCV,
    BC_OP.BC_OP_IFUNCV,
    BC_OP.BC_OP_JFUNCV,
    BC_OP.BC_OP_FUNCC,
    BC_OP.BC_OP_FUNCCW,
}


def get_op_type(byte: int, version: int) -> BC_OP:
    if version == BC_VERSION_1 and byte >= BC_OP.BC_OP_ISTYPE:
        if byte >= BC_OP.BC_OP_TGETR - 2:
            if byte >= BC_OP.BC_OP_TSETR - 3:
                byte += 4
            else:
                byte += 3
        else:
            byte += 2
    return BC_OP(byte)


def is_op_abc_format(instruction: BC_OP) -> bool:
    return instruction in ABC_FORMAT_OPS


@dataclass
class Instruction:
    type: BC_OP = BC_OP.BC_OP_INVALID
    a: int = 0
    b: int = 0
    c: int = 0
    d: int = 0


@dataclass
class TableConstant:
    type: BC_KTAB = BC_KTAB.BC_KTAB_NIL
    integer: int = 0
    number: int = 0
    string: str = ""


@dataclass
class TableNode:
    key: TableConstant = field(default_factory=TableConstant)
    value: TableConstant = field(default_factory=TableConstant)


@dataclass
class Constant:
    type: BC_KGC = BC_KGC.BC_KGC_CHILD
    prototype: Optional["Prototype"] = None
    array: list[TableConstant] = field(default_factory=list)
    table: list[TableNode] = field(default_factory=list)
    cdata: int = 0
    string: str = ""


@dataclass
class NumberConstant:
    type: BC_KNUM = BC_KNUM.BC_KNUM_INT
    integer: int = 0
    number: int = 0


@dataclass
class VariableInfo:
    type: BC_VAR = BC_VAR.BC_VAR_END
    name: str = ""
    is_parameter: bool = False
    scope_begin: int = 0
    scope_end: int = 0


@dataclass
class PrototypeHeader:
    flags: int = 0
    parameters: int = 0
    framesize: int = 0
    has_debug_info: bool = False
    first_line: int = 0
    line_count: int = 0


class Prototype:
    def __init__(self, bytecode: "Bytecode") -> None:
        self.bytecode = bytecode
        self.header = PrototypeHeader()
        self.instructions: list[Instruction] = []
        self.upvalues: list[int] = []
        self.constants: list[Constant] = []
        self.number_constants: list[NumberConstant] = []
        self.line_map: list[int] = []
        self.upvalue_names: list[str] = []
        self.variable_infos: list[VariableInfo] = []
        self.prototype_size = 0

    def __call__(self, unlinked_prototypes: list["Prototype"]) -> None:
        verbose_push(f"Prototype parse start (buffer={len(self.bytecode.file_buffer)} bytes)")
        try:
            self.read_header()
            self.read_instructions()
            self.read_upvalues()
            self.read_constants(unlinked_prototypes)
            self.read_number_constants()
            self.read_debug_info()
            decompiler_assert(
                self.prototype_size == len(self.bytecode.file_buffer),
                "Prototype has unread bytes left",
                self.bytecode.file_path,
                "Bytecode::Prototype::operator()",
                __file__,
                0,
            )
            unlinked_prototypes.append(self)
        finally:
            verbose_pop("Prototype parse done")

    def get_next_byte(self) -> int:
        buf = self.bytecode.file_buffer
        pos = self.prototype_size
        if pos >= len(buf):
            raise DecompilerError(
                "Prototype read would exceed end of buffer",
                self.bytecode.file_path,
                "Bytecode::Prototype::get_next_byte",
            )
        self.prototype_size = pos + 1
        return buf[pos]

    def get_uleb128(self) -> int:
        buf = self.bytecode.file_buffer
        pos = self.prototype_size
        byte = buf[pos]
        pos += 1
        if byte < 0x80:
            self.prototype_size = pos
            return byte
        uleb128 = byte & 0x7F
        bit_shift = 0
        while True:
            bit_shift += 7
            byte = buf[pos]
            pos += 1
            uleb128 |= (byte & 0x7F) << bit_shift
            if byte < 0x80:
                break
        self.prototype_size = pos
        return uleb128

    def get_uleb128_33(self) -> int:
        buf = self.bytecode.file_buffer
        pos = self.prototype_size
        first = buf[pos]
        pos += 1
        uleb128_33 = first >> 1
        if uleb128_33 < 0x40:
            self.prototype_size = pos
            return uleb128_33
        uleb128_33 &= 0x3F
        bit_shift = -1
        while True:
            bit_shift += 7
            byte = buf[pos]
            pos += 1
            uleb128_33 |= (byte & 0x7F) << bit_shift
            if byte < 0x80:
                break
        self.prototype_size = pos
        return uleb128_33

    def get_bytes_as_string(self, size: int) -> str:
        """Read *size* bytes from the buffer and return as a latin-1 string.
        Much faster than calling get_next_byte() in a loop."""
        pos = self.prototype_size
        end = pos + size
        s = self.bytecode.file_buffer[pos:end].decode("latin-1")
        self.prototype_size = end
        return s

    def get_string(self) -> str:
        buf = self.bytecode.file_buffer
        start = self.prototype_size
        pos = start
        while buf[pos] != 0:
            pos += 1
        self.prototype_size = pos + 1  # skip the NUL
        return buf[start:pos].decode("latin-1")

    def get_table_constant(self) -> TableConstant:
        table_constant = TableConstant()
        type_value = self.get_uleb128()
        if type_value in (
            BC_KTAB.BC_KTAB_NIL,
            BC_KTAB.BC_KTAB_FALSE,
            BC_KTAB.BC_KTAB_TRUE,
        ):
            table_constant.type = BC_KTAB(type_value)
        elif type_value == BC_KTAB.BC_KTAB_INT:
            table_constant.type = BC_KTAB.BC_KTAB_INT
            table_constant.integer = self.get_uleb128()
        elif type_value == BC_KTAB.BC_KTAB_NUM:
            table_constant.type = BC_KTAB.BC_KTAB_NUM
            table_constant.number = self.get_uleb128()
            table_constant.number |= self.get_uleb128() << 32
        else:
            table_constant.type = BC_KTAB.BC_KTAB_STR
            size = type_value - BC_KGC.BC_KGC_STR
            table_constant.string = self.get_bytes_as_string(size)
        return table_constant

    def read_header(self) -> None:
        self.header.flags = self.get_next_byte()
        decompiler_assert(
            not (self.header.flags & ~(BC_PROTO_CHILD | BC_PROTO_VARARG | BC_PROTO_FFI)),
            f"Prototype has invalid flags ({byte_to_string(self.header.flags)})",
            self.bytecode.file_path,
            "Bytecode::Prototype::read_header",
            __file__,
            0,
        )
        self.header.parameters = self.get_next_byte()
        self.header.framesize = self.get_next_byte()
        self.upvalues = [0] * self.get_next_byte()
        self.constants = [Constant() for _ in range(self.get_uleb128())]
        self.number_constants = [NumberConstant() for _ in range(self.get_uleb128())]
        self.instructions = [Instruction() for _ in range(self.get_uleb128())]
        decompiler_assert(
            len(self.instructions) > 0,
            "Prototype has no instructions",
            self.bytecode.file_path,
            "Bytecode::Prototype::read_header",
            __file__,
            0,
        )
        if (self.bytecode.header_flags & BC_F_STRIP) or (self.get_uleb128() == 0):
            if _verbose_enabled:
                verbose_log(
                    "Header parsed: "
                    f"flags=0x{self.header.flags:02X}, params={self.header.parameters}, "
                    f"framesize={self.header.framesize}, upvalues={len(self.upvalues)}, "
                    f"const={len(self.constants)}, numconst={len(self.number_constants)}, "
                    f"instructions={len(self.instructions)}, debug=False"
                )
            return
        self.header.has_debug_info = True
        self.header.first_line = self.get_uleb128()
        self.header.line_count = self.get_uleb128()
        if _verbose_enabled:
            verbose_log(
                "Header parsed: "
                f"flags=0x{self.header.flags:02X}, params={self.header.parameters}, "
                f"framesize={self.header.framesize}, upvalues={len(self.upvalues)}, "
                f"const={len(self.constants)}, numconst={len(self.number_constants)}, "
                f"instructions={len(self.instructions)}, debug=True, "
                f"first_line={self.header.first_line}, line_count={self.header.line_count}"
            )

    def read_instructions(self) -> None:
        verbose_push(f"Decode {len(self.instructions)} instruction(s)")
        for i in range(len(self.instructions)):
            op = get_op_type(self.get_next_byte(), self.bytecode.header_version)
            decompiler_assert(
                op < BC_OP.BC_OP_INVALID,
                f"Prototype has invalid instruction ({byte_to_string(int(op))})",
                self.bytecode.file_path,
                "Bytecode::Prototype::read_instructions",
                __file__,
                0,
            )
            decompiler_assert(
                op not in UNSUPPORTED_OPS,
                f"Prototype has unsupported instruction ({byte_to_string(int(op))})",
                self.bytecode.file_path,
                "Bytecode::Prototype::read_instructions",
                __file__,
                0,
            )
            self.instructions[i].type = op
            self.instructions[i].a = self.get_next_byte()
            if is_op_abc_format(op):
                self.instructions[i].c = self.get_next_byte()
                self.instructions[i].b = self.get_next_byte()
                if _verbose_enabled:
                    verbose_log(
                        f"ins[{i}] {op.name} A={self.instructions[i].a} "
                        f"B={self.instructions[i].b} C={self.instructions[i].c}"
                    )
            else:
                self.instructions[i].d = self.get_next_byte()
                self.instructions[i].d |= self.get_next_byte() << 8
                if _verbose_enabled:
                    verbose_log(
                        f"ins[{i}] {op.name} A={self.instructions[i].a} D={self.instructions[i].d}"
                    )
        verbose_pop("Instruction decode done")

    def read_upvalues(self) -> None:
        verbose_push(f"Read {len(self.upvalues)} upvalue descriptor(s)")
        for i in range(len(self.upvalues)):
            value = self.get_next_byte()
            value |= self.get_next_byte() << 8
            self.upvalues[i] = value
            if _verbose_enabled:
                verbose_log(f"upvalue[{i}] = 0x{value:04X}")
        verbose_pop("Upvalues read")

    def read_constants(self, unlinked_prototypes: list["Prototype"]) -> None:
        verbose_push(f"Read {len(self.constants)} GC constant(s)")
        for i in range(len(self.constants)):
            type_value = self.get_uleb128()
            constant = self.constants[i]
            if type_value == BC_KGC.BC_KGC_CHILD:
                constant.type = BC_KGC.BC_KGC_CHILD
                decompiler_assert(
                    len(unlinked_prototypes) > 0,
                    "Failed to link child prototype",
                    self.bytecode.file_path,
                    "Bytecode::Prototype::read_constants",
                    __file__,
                    0,
                )
                constant.prototype = unlinked_prototypes.pop()
                if _verbose_enabled:
                    verbose_log(f"const[{i}] CHILD prototype linked")
                continue
            if type_value == BC_KGC.BC_KGC_TAB:
                constant.type = BC_KGC.BC_KGC_TAB
                array_size = self.get_uleb128()
                table_size = self.get_uleb128()
                constant.array = [self.get_table_constant() for _ in range(array_size)]
                constant.table = []
                for _ in range(table_size):
                    node = TableNode()
                    node.key = self.get_table_constant()
                    node.value = self.get_table_constant()
                    constant.table.append(node)
                if _verbose_enabled:
                    verbose_log(
                        f"const[{i}] TAB array={array_size} hash={table_size}"
                    )
                continue
            if type_value == BC_KGC.BC_KGC_COMPLEX:
                decompiler_assert(
                    self.get_uleb128() == 0 and self.get_uleb128() == 0,
                    "Prototype has invalid cdata constant",
                    self.bytecode.file_path,
                    "Bytecode::Prototype::read_constants",
                    __file__,
                    0,
                )
            if type_value in (
                BC_KGC.BC_KGC_I64,
                BC_KGC.BC_KGC_U64,
                BC_KGC.BC_KGC_COMPLEX,
            ):
                constant.type = BC_KGC(type_value)
                constant.cdata = self.get_uleb128()
                constant.cdata |= self.get_uleb128() << 32
                if _verbose_enabled:
                    verbose_log(f"const[{i}] {constant.type.name} cdata=0x{constant.cdata:016X}")
                continue
            constant.type = BC_KGC.BC_KGC_STR
            size = type_value - BC_KGC.BC_KGC_STR
            constant.string = self.get_bytes_as_string(size)
            if _verbose_enabled:
                verbose_log(f"const[{i}] STR len={size}")
        verbose_pop("GC constants read")

    def read_number_constants(self) -> None:
        verbose_push(f"Read {len(self.number_constants)} numeric constant(s)")
        for i in range(len(self.number_constants)):
            number_constant = self.number_constants[i]
            is_num = self.bytecode.file_buffer[self.prototype_size] & 0x01
            if is_num:
                number_constant.type = BC_KNUM.BC_KNUM_NUM
                number_constant.number = self.get_uleb128_33()
                number_constant.number |= self.get_uleb128() << 32
                if _verbose_enabled:
                    verbose_log(
                        f"numconst[{i}] NUM raw=0x{number_constant.number:016X}"
                    )
            else:
                number_constant.type = BC_KNUM.BC_KNUM_INT
                number_constant.integer = self.get_uleb128_33()
                if _verbose_enabled:
                    verbose_log(f"numconst[{i}] INT value={number_constant.integer}")
        verbose_pop("Numeric constants read")

    def read_debug_info(self) -> None:
        if not self.header.has_debug_info:
            verbose_log("Debug info: stripped")
            return
        verbose_push("Read debug info")
        self.line_map = [0] * len(self.instructions)
        if self.header.line_count < 256:
            for i in range(len(self.line_map)):
                self.line_map[i] = self.get_next_byte()
        elif self.header.line_count < 65536:
            for i in range(len(self.line_map)):
                value = self.get_next_byte()
                value |= self.get_next_byte() << 8
                self.line_map[i] = value
        else:
            for i in range(len(self.line_map)):
                value = self.get_next_byte()
                value |= self.get_next_byte() << 8
                value |= self.get_next_byte() << 16
                value |= self.get_next_byte() << 24
                self.line_map[i] = value

        self.upvalue_names = [self.get_string() for _ in range(len(self.upvalues))]
        scope_offset = 0
        parameter_count = 0
        while True:
            byte = self.get_next_byte()
            if byte == 0:
                break
            info = VariableInfo()
            if byte >= BC_VAR.BC_VAR_STR:
                info.type = BC_VAR.BC_VAR_STR
                info.name = chr(byte) + self.get_string()
            else:
                info.type = BC_VAR(byte)
            scope_offset += self.get_uleb128()
            decompiler_assert(
                scope_offset != 1,
                "Prototype variable has invalid scope",
                self.bytecode.file_path,
                "Bytecode::Prototype::read_debug_info",
                __file__,
                0,
            )
            if scope_offset == 0:
                info.is_parameter = True
                parameter_count += 1
                info.scope_end = self.get_uleb128() - 2
            else:
                info.scope_begin = scope_offset - 2
                info.scope_end = info.scope_begin + self.get_uleb128()
            self.variable_infos.append(info)
        decompiler_assert(
            parameter_count == self.header.parameters,
            "Prototype parameter count does not\nmatch with debug info",
            self.bytecode.file_path,
            "Bytecode::Prototype::read_debug_info",
            __file__,
            0,
        )
        if _verbose_enabled:
            verbose_log(
                f"Debug info parsed: lines={len(self.line_map)}, "
                f"upvalue_names={len(self.upvalue_names)}, locals={len(self.variable_infos)}"
            )
        verbose_pop("Debug info read")


class Bytecode:
    MIN_PROTO_SIZE = 11
    MIN_FILE_SIZE = MIN_PROTO_SIZE + 7

    def __init__(self, file_path: str) -> None:
        self.file_path = file_path
        self.header_version = 0
        self.header_flags = 0
        self.header_chunkname = ""
        self.main: Optional[Prototype] = None
        self.prototypes_total_size = 0
        self._file_data = b""
        self._offset = 0
        self.file_size = 0
        self.bytes_unread = 0
        self.file_buffer = b""
        self.prototypes: list[Prototype] = []

    def __call__(self) -> None:
        verbose_push(f"Bytecode parse: {self.file_path}")
        try:
            print_progress_bar()
            self.open_file()
            self.read_header()
            self.prototypes_total_size = self.bytes_unread - 1
            self.read_prototypes()
            self.file_buffer = b""
            erase_progress_bar()
        finally:
            verbose_pop("Bytecode parse complete")

    def open_file(self) -> None:
        path = Path(self.file_path)
        decompiler_assert(
            path.exists() and path.is_file(),
            "Unable to open file",
            self.file_path,
            "Bytecode::open_file",
            __file__,
            0,
        )
        self._file_data = path.read_bytes()
        self.file_size = len(self._file_data)
        decompiler_assert(
            self.file_size >= self.MIN_FILE_SIZE,
            "File is too small or empty",
            self.file_path,
            "Bytecode::open_file",
            __file__,
            0,
        )
        self._offset = 0
        self.bytes_unread = self.file_size
        verbose_log(f"Opened file ({self.file_size} bytes)")

    def read_file(self, byte_count: int) -> None:
        decompiler_assert(
            self.bytes_unread >= byte_count,
            "Read would exceed end of file",
            self.file_path,
            "Bytecode::read_file",
            __file__,
            0,
        )
        start = self._offset
        end = self._offset + byte_count
        self.file_buffer = self._file_data[start:end]
        self._offset = end
        self.bytes_unread -= byte_count

    def read_uleb128(self) -> int:
        self.read_file(1)
        uleb128 = self.file_buffer[0]
        if uleb128 >= 0x80:
            uleb128 &= 0x7F
            bit_shift = 0
            while True:
                bit_shift += 7
                self.read_file(1)
                byte = self.file_buffer[0]
                uleb128 |= (byte & 0x7F) << bit_shift
                if byte < 0x80:
                    break
        return uleb128

    def buffer_next_block(self) -> bool:
        byte_count = self.read_uleb128()
        if byte_count == 0:
            decompiler_assert(
                self.bytes_unread == 0,
                "Read unexpectedly reached end of file",
                self.file_path,
                "Bytecode::buffer_next_block",
                __file__,
                0,
            )
            return False
        self.read_file(byte_count)
        return True

    def read_header(self) -> None:
        self.read_file(5)
        decompiler_assert(
            self.file_buffer[:3] == BC_HEADER,
            "Invalid header:\n"
            f"Expected bytes {byte_to_string(BC_HEADER[0])} {byte_to_string(BC_HEADER[1])} {byte_to_string(BC_HEADER[2])}, "
            f"got {byte_to_string(self.file_buffer[0])} {byte_to_string(self.file_buffer[1])} {byte_to_string(self.file_buffer[2])}"
            "\n\nFile does not contain valid LuaJIT bytecode",
            self.file_path,
            "Bytecode::read_header",
            __file__,
            0,
        )
        self.header_version = self.file_buffer[3]
        decompiler_assert(
            self.header_version in (BC_VERSION_1, BC_VERSION_2),
            f"Invalid bytecode version ({byte_to_string(self.file_buffer[3])})",
            self.file_path,
            "Bytecode::read_header",
            __file__,
            0,
        )
        self.header_flags = self.file_buffer[4]
        supported_flags = BC_F_BE | BC_F_STRIP | BC_F_FFI | (
            BC_F_FR2 if self.header_version == BC_VERSION_2 else 0
        )
        decompiler_assert(
            not (self.header_flags & ~supported_flags),
            f"Invalid flags ({byte_to_string(self.header_flags)})",
            self.file_path,
            "Bytecode::read_header",
            __file__,
            0,
        )
        decompiler_assert(
            not (self.header_flags & BC_F_BE),
            "Big endian support not implemented",
            self.file_path,
            "Bytecode::read_header",
            __file__,
            0,
        )
        if self.header_flags & BC_F_STRIP:
            verbose_log(
                "Header parsed: "
                f"version={self.header_version}, flags=0x{self.header_flags:02X}, stripped=True"
            )
            return
        self.read_file(self.read_uleb128())
        self.header_chunkname = self.file_buffer.decode("latin1")
        verbose_log(
            "Header parsed: "
            f"version={self.header_version}, flags=0x{self.header_flags:02X}, "
            f"stripped=False, chunkname={self.header_chunkname!r}"
        )

    def read_prototypes(self) -> None:
        verbose_push("Read prototypes")
        unlinked_prototypes: list[Prototype] = []
        prototype_index = 0
        while self.buffer_next_block():
            decompiler_assert(
                len(self.file_buffer) >= self.MIN_PROTO_SIZE,
                "Prototype is too short",
                self.file_path,
                "Bytecode::read_prototypes",
                __file__,
                0,
            )
            prototype = Prototype(self)
            self.prototypes.append(prototype)
            verbose_log(
                f"prototype[{prototype_index}] block_size={len(self.file_buffer)} bytes"
            )
            prototype(unlinked_prototypes)
            prototype_index += 1
            print_progress_bar(
                self.prototypes_total_size - self.bytes_unread - 1,
                self.prototypes_total_size,
            )
        decompiler_assert(
            len(unlinked_prototypes) == 1,
            "Failed to link main prototype",
            self.file_path,
            "Bytecode::read_prototypes",
            __file__,
            0,
        )
        self.main = unlinked_prototypes[-1]
        decompiler_assert(
            bool(self.main.header.flags & BC_PROTO_VARARG)
            and self.main.header.parameters == 0
            and len(self.main.upvalues) == 0,
            "Main prototype has invalid header",
            self.file_path,
            "Bytecode::read_prototypes",
            __file__,
            0,
        )
        verbose_log(f"Main prototype resolved (total prototypes={len(self.prototypes)})")
        verbose_pop("Prototype read complete")


INVALID_ID = 0xFFFFFFFF


class CONSTANT_TYPE(IntEnum):
    INVALID_CONSTANT = 0
    NIL_CONSTANT = 1
    BOOL_CONSTANT = 2
    NUMBER_CONSTANT = 3


class AST_EXPRESSION(IntEnum):
    AST_EXPRESSION_CONSTANT = 0
    AST_EXPRESSION_VARARG = 1
    AST_EXPRESSION_FUNCTION = 2
    AST_EXPRESSION_VARIABLE = 3
    AST_EXPRESSION_FUNCTION_CALL = 4
    AST_EXPRESSION_TABLE = 5
    AST_EXPRESSION_BINARY_OPERATION = 6
    AST_EXPRESSION_UNARY_OPERATION = 7


class AST_CONSTANT(IntEnum):
    AST_CONSTANT_NIL = 0
    AST_CONSTANT_FALSE = 1
    AST_CONSTANT_TRUE = 2
    AST_CONSTANT_NUMBER = 3
    AST_CONSTANT_CDATA_SIGNED = 4
    AST_CONSTANT_CDATA_UNSIGNED = 5
    AST_CONSTANT_CDATA_IMAGINARY = 6
    AST_CONSTANT_STRING = 7


class AST_VARIABLE(IntEnum):
    AST_VARIABLE_SLOT = 0
    AST_VARIABLE_UPVALUE = 1
    AST_VARIABLE_GLOBAL = 2
    AST_VARIABLE_TABLE_INDEX = 3


class AST_BINARY_OPERATION(IntEnum):
    AST_BINARY_ADDITION = 0
    AST_BINARY_SUBTRACTION = 1
    AST_BINARY_MULTIPLICATION = 2
    AST_BINARY_DIVISION = 3
    AST_BINARY_EXPONENTATION = 4
    AST_BINARY_MODULO = 5
    AST_BINARY_CONCATENATION = 6
    AST_BINARY_LESS_THAN = 7
    AST_BINARY_LESS_EQUAL = 8
    AST_BINARY_GREATER_THEN = 9
    AST_BINARY_GREATER_EQUAL = 10
    AST_BINARY_EQUAL = 11
    AST_BINARY_NOT_EQUAL = 12
    AST_BINARY_AND = 13
    AST_BINARY_OR = 14


class AST_UNARY_OPERATION(IntEnum):
    AST_UNARY_MINUS = 0
    AST_UNARY_NOT = 1
    AST_UNARY_LENGTH = 2


class AST_STATEMENT(IntEnum):
    AST_STATEMENT_EMPTY = 0
    AST_STATEMENT_INSTRUCTION = 1
    AST_STATEMENT_RETURN = 2
    AST_STATEMENT_CONDITION = 3
    AST_STATEMENT_GOTO = 4
    AST_STATEMENT_NUMERIC_FOR = 5
    AST_STATEMENT_GENERIC_FOR = 6
    AST_STATEMENT_LOOP = 7
    AST_STATEMENT_BREAK = 8
    AST_STATEMENT_DECLARATION = 9
    AST_STATEMENT_ASSIGNMENT = 10
    AST_STATEMENT_FUNCTION_CALL = 11
    AST_STATEMENT_IF = 12
    AST_STATEMENT_ELSE = 13
    AST_STATEMENT_WHILE = 14
    AST_STATEMENT_REPEAT = 15
    AST_STATEMENT_DO = 16
    AST_STATEMENT_LABEL = 17


class ScopeCell:
    def __init__(self, scope: Optional["SlotScope"] = None) -> None:
        self.scope = scope


@dataclass
class AstConstant:
    type: AST_CONSTANT = AST_CONSTANT.AST_CONSTANT_NIL
    number: float = 0.0
    signed_integer: int = 0
    unsigned_integer: int = 0
    string: str = ""
    is_name: bool = False


@dataclass
class AstVariable:
    type: AST_VARIABLE = AST_VARIABLE.AST_VARIABLE_SLOT
    slot: int = 0
    slot_scope: Optional[ScopeCell] = None
    name: str = ""
    table: Optional["Expression"] = None
    table_index: Optional["Expression"] = None
    is_multres: bool = False
    multres_index: int = 0


@dataclass
class AstFunctionCall:
    function: Optional["Expression"] = None
    arguments: list["Expression"] = field(default_factory=list)
    multres_argument: Optional["Expression"] = None
    is_method: bool = False
    return_count: int = 0


@dataclass
class AstTableField:
    key: Optional["Expression"] = None
    value: Optional["Expression"] = None


@dataclass
class AstTableConstants:
    list: list["Expression"] = field(default_factory=builtins.list)
    fields: list[AstTableField] = field(default_factory=builtins.list)


@dataclass
class AstTable:
    constants: AstTableConstants = field(default_factory=AstTableConstants)
    fields: list[AstTableField] = field(default_factory=list)
    multres_index: int = 0
    multres_field: Optional["Expression"] = None


@dataclass
class AstBinaryOperation:
    type: AST_BINARY_OPERATION = AST_BINARY_OPERATION.AST_BINARY_ADDITION
    left_operand: Optional["Expression"] = None
    right_operand: Optional["Expression"] = None


@dataclass
class AstUnaryOperation:
    type: AST_UNARY_OPERATION = AST_UNARY_OPERATION.AST_UNARY_MINUS
    operand: Optional["Expression"] = None


class Expression:
    __slots__ = (
        "type", "constant", "function", "variable", "function_call",
        "table", "binary_operation", "unary_operation", "return_count",
    )

    def __init__(self, type_: AST_EXPRESSION) -> None:
        self.type = type_
        self.constant: Optional[AstConstant] = None
        self.function: Optional["Function"] = None
        self.variable: Optional[AstVariable] = None
        self.function_call: Optional[AstFunctionCall] = None
        self.table: Optional[AstTable] = None
        self.binary_operation: Optional[AstBinaryOperation] = None
        self.unary_operation: Optional[AstUnaryOperation] = None
        self.return_count: int = 0
        # Allocate the sub-object for the given type directly (no set_type call).
        if type_ == AST_EXPRESSION.AST_EXPRESSION_CONSTANT:
            self.constant = AstConstant()
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
            self.variable = AstVariable()
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
            self.function_call = AstFunctionCall()
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_TABLE:
            self.table = AstTable()
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            self.binary_operation = AstBinaryOperation()
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            self.unary_operation = AstUnaryOperation()

    def set_type(self, type_: AST_EXPRESSION) -> None:
        self.type = type_
        self.constant = None
        self.function = None
        self.variable = None
        self.function_call = None
        self.table = None
        self.binary_operation = None
        self.unary_operation = None
        self.return_count = 0
        if type_ == AST_EXPRESSION.AST_EXPRESSION_CONSTANT:
            self.constant = AstConstant()
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_VARARG:
            self.return_count = 0
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
            self.variable = AstVariable()
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
            self.function_call = AstFunctionCall()
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_TABLE:
            self.table = AstTable()
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            self.binary_operation = AstBinaryOperation()
        elif type_ == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            self.unary_operation = AstUnaryOperation()

    def assign_from(self, other: "Expression") -> None:
        if self is other:
            return
        self.type = other.type
        self.constant = other.constant
        self.function = other.function
        self.variable = other.variable
        self.function_call = other.function_call
        self.table = other.table
        self.binary_operation = other.binary_operation
        self.unary_operation = other.unary_operation
        self.return_count = other.return_count


@dataclass
class StatementInstruction:
    type: BC_OP = BC_OP.BC_OP_INVALID
    a: int = 0
    b: int = 0
    c: int = 0
    d: int = 0
    id: int = INVALID_ID
    target: int = INVALID_ID
    label: int = INVALID_ID


@dataclass
class StatementConditionFlags:
    allow_slot_swap: bool = False
    swapped: bool = False


@dataclass
class AssignmentInfo:
    is_potential_method: bool = False
    is_table_constructor: bool = False
    forward_declaration: bool = False
    allowed_constant_type: CONSTANT_TYPE = CONSTANT_TYPE.NUMBER_CONSTANT
    variables: list[AstVariable] = field(default_factory=list)
    expressions: list[Expression] = field(default_factory=list)
    open_slots: list[Expression] = field(default_factory=list)
    multres_return: Optional[Expression] = None

    def register_slots(self, *expressions: Expression) -> None:
        for expression in expressions:
            self.open_slots.append(expression)


class Statement:
    def __init__(self, type_: AST_STATEMENT) -> None:
        self.type = type_
        self.instruction = StatementInstruction()
        self.function: Optional["Function"] = None
        self.block: list["Statement"] = []
        self.locals: Optional["Local"] = None
        self.condition = StatementConditionFlags()
        self.assignment = AssignmentInfo()


@dataclass
class Local:
    names: list[str] = field(default_factory=list)
    base_slot: int = 0
    scope_begin: int = INVALID_ID
    scope_end: int = INVALID_ID
    exclude_block: bool = False


@dataclass
class SlotScope:
    slot_scope: ScopeCell = field(default_factory=ScopeCell)
    merged_scopes: list[ScopeCell] = field(default_factory=list)
    name: str = ""
    scope_begin: int = INVALID_ID
    scope_end: int = INVALID_ID
    usages: int = 0


class UpvalueInfoType(IntEnum):
    JUMP = 0
    UPVALUES = 1
    UPVALUE_CLOSE = 2


@dataclass
class UpvalueInfo:
    type: UpvalueInfoType
    id: int = INVALID_ID
    target: int = INVALID_ID
    upvalues: list[int] = field(default_factory=list)
    base_slot: int = 0


@dataclass
class UpvalueScope:
    slot: int = 0
    min_scope_begin: int = INVALID_ID
    min_scope_end: int = INVALID_ID


@dataclass
class SlotInfo:
    is_parameter: bool = False
    active_slot_scope: Optional[ScopeCell] = None
    min_scope_begin: int = INVALID_ID
    slot_scopes: list[ScopeCell] = field(default_factory=list)


class SlotScopeCollector:
    def __init__(self) -> None:
        self.upvalue_infos: list[UpvalueInfo] = []
        self.upvalue_scopes: list[UpvalueScope] = []
        self.slot_infos: list[SlotInfo] = []
        self.slot_scopes: list[SlotScope] = []
        self.previous_id: int = INVALID_ID

    def new_slot_scope(self) -> ScopeCell:
        scope = SlotScope()
        cell = ScopeCell(scope)
        scope.slot_scope = cell
        self.slot_scopes.append(scope)
        return cell

    def add_upvalue_info(self, id_: int, type_: UpvalueInfoType) -> int:
        for i in range(len(self.upvalue_infos)):
            if id_ > self.upvalue_infos[i].id:
                continue
            info = UpvalueInfo(type=type_, id=id_)
            self.upvalue_infos.insert(i, info)
            return i
        self.upvalue_infos.append(UpvalueInfo(type=type_, id=id_))
        return len(self.upvalue_infos) - 1

    def add_upvalues(self, id_: int, upvalues: list[int]) -> None:
        self.upvalue_infos[self.add_upvalue_info(id_, UpvalueInfoType.UPVALUES)].upvalues = list(
            upvalues
        )

    def add_jump(self, id_: int, target: int) -> None:
        self.upvalue_infos[self.add_upvalue_info(id_, UpvalueInfoType.JUMP)].target = target

    def add_upvalue_close(self, id_: int, target: int, base_slot: int) -> None:
        index = self.add_upvalue_info(id_, UpvalueInfoType.UPVALUE_CLOSE)
        self.upvalue_infos[index].target = target
        self.upvalue_infos[index].base_slot = base_slot

    def add_loop(self, id_: int, target: int) -> None:
        index = self.add_upvalue_info(id_, UpvalueInfoType.JUMP)
        self.upvalue_infos[index].target = target
        while index + 1 < len(self.upvalue_infos) and self.upvalue_infos[index + 1].id < target:
            index += 1
        self.upvalue_infos.insert(
            index + 1,
            UpvalueInfo(type=UpvalueInfoType.JUMP, id=target - 1, target=id_),
        )

    def add_upvalue_scope(self, slot: int, min_scope_begin: int, min_scope_end: int) -> None:
        for i in range(len(self.upvalue_scopes)):
            if min_scope_end > self.upvalue_scopes[i].min_scope_end:
                continue
            self.upvalue_scopes.insert(
                i,
                UpvalueScope(
                    slot=slot,
                    min_scope_begin=min_scope_begin,
                    min_scope_end=min_scope_end,
                ),
            )
            return
        self.upvalue_scopes.append(
            UpvalueScope(slot=slot, min_scope_begin=min_scope_begin, min_scope_end=min_scope_end)
        )

    def build_upvalue_scopes(self) -> None:
        for i in range(len(self.upvalue_infos) - 1, -1, -1):
            if self.upvalue_infos[i].type != UpvalueInfoType.UPVALUES:
                continue
            for j in range(len(self.upvalue_infos[i].upvalues) - 1, -1, -1):
                index = i
                min_scope_begin = self.upvalue_infos[i].id
                min_scope_end = self.upvalue_infos[i].id
                for k in range(i + 1, len(self.upvalue_infos)):
                    info_k = self.upvalue_infos[k]
                    if info_k.type == UpvalueInfoType.UPVALUE_CLOSE:
                        if self.upvalue_infos[i].upvalues[j] >= info_k.base_slot:
                            if min_scope_end > info_k.id:
                                continue
                            min_scope_end = info_k.id
                            break
                        # UPVALUE_CLOSE with upvalues[j] < baseSlot
                        # falls through to JUMP handling
                    # Handle both JUMP type and UPVALUE_CLOSE fallthrough
                    if info_k.type in (UpvalueInfoType.JUMP, UpvalueInfoType.UPVALUE_CLOSE):
                        if min_scope_end < info_k.target:
                            min_scope_end = info_k.target
                        elif min_scope_begin >= info_k.target:
                            min_scope_begin = info_k.target - 1
                            l = index
                            while l > 0 and min_scope_begin < self.upvalue_infos[l - 1].id:
                                l -= 1
                                info_l = self.upvalue_infos[l]
                                if info_l.type == UpvalueInfoType.UPVALUE_CLOSE:
                                    if self.upvalue_infos[i].upvalues[j] >= info_l.base_slot:
                                        continue
                                # Both JUMP and UPVALUE_CLOSE (when
                                # upvalues[j] < baseSlot) process the target
                                if info_l.type in (UpvalueInfoType.JUMP, UpvalueInfoType.UPVALUE_CLOSE):
                                    if min_scope_end < info_l.target:
                                        min_scope_end = info_l.target
                                    elif min_scope_begin >= info_l.target:
                                        min_scope_begin = info_l.target - 1
                            index = l
                    # Continue to the next scope entry.
                self.add_upvalue_scope(
                    self.upvalue_infos[i].upvalues[j], min_scope_begin, min_scope_end
                )

    def begin_scope(self, slot: int, id_: int) -> None:
        if self.slot_infos[slot].active_slot_scope is not None:
            return
        cell = self.new_slot_scope()
        self.slot_infos[slot].slot_scopes.append(cell)
        self.slot_infos[slot].active_slot_scope = cell
        cell.scope.scope_end = id_

    def begin_upvalue_scopes(self, id_: int) -> None:
        while self.upvalue_scopes and self.upvalue_scopes[-1].min_scope_end >= id_:
            scope = self.upvalue_scopes[-1]
            if scope.min_scope_begin <= id_:
                self.begin_scope(scope.slot, id_)
                self.extend_scope(scope.slot, scope.min_scope_begin)
            self.upvalue_scopes.pop()

    def add_to_scope(self, slot: int, id_: int) -> ScopeCell:
        self.begin_scope(slot, id_)
        cell = self.slot_infos[slot].active_slot_scope
        decompiler_assert(cell is not None, "Scope not opened")
        cell.scope.usages += 1
        return cell

    def close_scope(self, slot: int, id_: int) -> ScopeCell:
        if self.slot_infos[slot].is_parameter or (
            self.slot_infos[slot].min_scope_begin != INVALID_ID
            and self.slot_infos[slot].min_scope_begin < id_
        ):
            return self.add_to_scope(slot, id_)
        self.begin_scope(slot, id_)
        cell = self.slot_infos[slot].active_slot_scope
        decompiler_assert(cell is not None, "Scope not opened")
        cell.scope.scope_begin = id_
        self.slot_infos[slot].active_slot_scope = None
        self.slot_infos[slot].min_scope_begin = INVALID_ID
        return cell

    def extend_scope(self, slot: int, id_: int) -> None:
        info = self.slot_infos[slot]
        if (
            not info.is_parameter
            and info.active_slot_scope is not None
            and (info.min_scope_begin == INVALID_ID or info.min_scope_begin > id_)
        ):
            info.min_scope_begin = id_

    def extend_scopes(self, id_: int) -> None:
        for i in range(len(self.slot_infos) - 1, -1, -1):
            self.extend_scope(i, id_)

    def merge_scopes(self, id_: int) -> None:
        for i in range(len(self.slot_infos) - 1, -1, -1):
            info = self.slot_infos[i]
            if info.is_parameter or info.active_slot_scope is None:
                continue
            # Preserve the backward scan's decrement-before-check order:
            # skip the active slot scope at the back and only merge older scopes.
            j = len(info.slot_scopes) - 2
            while j >= 0 and info.slot_scopes[j].scope.scope_begin <= id_:
                active_scope = info.active_slot_scope.scope
                merged_scope = info.slot_scopes[j].scope
                active_scope.scope_end = merged_scope.scope_end
                active_scope.usages += merged_scope.usages + 1
                for merged_cell in merged_scope.merged_scopes:
                    merged_cell.scope = active_scope
                active_scope.merged_scopes.extend(merged_scope.merged_scopes)
                active_scope.merged_scopes.append(merged_scope.slot_scope)
                merged_scope.slot_scope.scope = active_scope
                info.slot_scopes[j].scope = active_scope
                info.slot_scopes.pop(j)
                j -= 1
            if info.active_slot_scope.scope.scope_end < id_:
                info.active_slot_scope.scope.scope_end = id_

    def assert_scopes_closed(self) -> bool:
        for i in range(len(self.slot_infos) - 1, -1, -1):
            if not self.slot_infos[i].is_parameter and self.slot_infos[i].active_slot_scope is not None:
                return False
        return True

    def remove_scope(self, slot: int, slot_scope: ScopeCell) -> None:
        scopes = self.slot_infos[slot].slot_scopes
        for i in range(len(scopes) - 1, -1, -1):
            if scopes[i] is slot_scope:
                scopes.pop(i)
                return


@dataclass
class FunctionUpvalue:
    slot: int = 0
    slot_scope: Optional[ScopeCell] = None
    local: bool = False


@dataclass
class FunctionLabel:
    name: str = ""
    target: int = INVALID_ID
    jump_ids: list[int] = field(default_factory=list)


class Function:
    def __init__(self, prototype: Prototype, level: int, ignore_debug_info: bool) -> None:
        self.prototype = prototype
        self.is_variadic = bool(prototype.header.flags & BC_PROTO_VARARG)
        self.level = level
        self.has_debug_info = (not ignore_debug_info) and prototype.header.has_debug_info
        self.id = 0
        self.assignment_slot_is_upvalue = False
        self.locals: list[Local] = []
        self.upvalues: list[FunctionUpvalue] = []
        self.labels: list[FunctionLabel] = []
        self.parameter_names: list[str] = []
        self.block: list[Statement] = []
        self.child_functions: list["Function"] = []
        self.used_globals: list[str] = []
        self.slot_scope_collector = SlotScopeCollector()
        self.slot_scope_collector.slot_infos = [SlotInfo() for _ in range(prototype.header.framesize)]
        for i in range(prototype.header.parameters - 1, -1, -1):
            info = self.slot_scope_collector.slot_infos[i]
            info.is_parameter = True
            info.active_slot_scope = self.slot_scope_collector.new_slot_scope()
        self.slot_scope_collector.previous_id = len(prototype.instructions)

    def get_constant(self, index: int) -> Constant:
        return self.prototype.constants[len(self.prototype.constants) - 1 - index]

    def get_number_constant(self, index: int) -> NumberConstant:
        return self.prototype.number_constants[index]

    def add_jump(self, id_: int, target: int) -> None:
        for i in range(len(self.labels)):
            if target > self.labels[i].target:
                continue
            if target != self.labels[i].target:
                self.labels.insert(i, FunctionLabel(target=target))
            for j in range(len(self.labels[i].jump_ids)):
                if id_ > self.labels[i].jump_ids[j]:
                    continue
                if id_ < self.labels[i].jump_ids[j]:
                    self.labels[i].jump_ids.insert(j, id_)
                return
            self.labels[i].jump_ids.append(id_)
            return
        label = FunctionLabel(target=target, jump_ids=[id_])
        self.labels.append(label)

    def remove_jump(self, id_: int, target: int) -> None:
        for i in range(len(self.labels) - 1, -1, -1):
            if self.labels[i].target != target:
                continue
            for j in range(len(self.labels[i].jump_ids) - 1, -1, -1):
                if self.labels[i].jump_ids[j] != id_:
                    continue
                self.labels[i].jump_ids.pop(j)
                return

    def get_label_from_id(self, id_: int) -> int:
        for i in range(len(self.labels) - 1, -1, -1):
            if self.labels[i].target < id_:
                break
            if self.labels[i].target == id_:
                return i
        return INVALID_ID

    def is_valid_label(self, label: int) -> bool:
        return label != INVALID_ID and len(self.labels[label].jump_ids) > 0

    def get_scope_begin_from_label(self, label: int, scope_end: int) -> int:
        scope_begin = self.labels[label].target - 1
        i = label
        while i < len(self.labels) and self.labels[i].target <= scope_end:
            if self.labels[i].jump_ids and self.labels[i].jump_ids[0] <= scope_begin:
                scope_begin = self.labels[i].jump_ids[0] - 1
            i += 1
        return scope_begin

    def get_scope_end_from_label(self, label: int) -> int:
        scope_end = self.labels[label].target
        i = label
        while i < len(self.labels) and self.labels[i].target <= scope_end:
            if self.labels[i].jump_ids and self.labels[i].jump_ids[-1] > scope_end:
                scope_end = self.labels[i].jump_ids[-1]
            i += 1
        return scope_end

    def is_valid_block_range(self, block_begin: int, block_end: int, ignore_front_label: bool) -> bool:
        for i in range(len(self.labels) - 1, -1, -1):
            if self.labels[i].target < block_begin:
                break
            if (
                self.labels[i].target <= block_end
                and self.labels[i].jump_ids
                and (
                    (
                        self.labels[i].jump_ids[0] < block_begin
                        and (self.labels[i].target != block_begin or not ignore_front_label)
                    )
                    or self.labels[i].jump_ids[-1] > block_end
                )
            ):
                return False
        return True


@dataclass
class BlockInfo:
    block: list[Statement]
    previous_block: Optional["BlockInfo"]
    index: int = INVALID_ID


class ConditionBuilderType(IntEnum):
    ASSIGNMENT = 0
    STATEMENT = 1


class ConditionNodeType(IntEnum):
    LESS_THAN = 0
    LESS_EQUAL = 1
    GREATER_THEN = 2
    GREATER_EQUAL = 3
    NOT_LESS_THAN = 4
    NOT_LESS_EQUAL = 5
    NOT_GREATER_THEN = 6
    NOT_GREATER_EQUAL = 7
    EQUAL = 8
    NOT_EQUAL = 9
    TRUTHY_TEST = 10
    FALSY_TEST = 11
    BOOL_TRUTHY_TEST = 12
    BOOL_FALSY_TEST = 13
    UNCONDITIONAL_TRUE = 14
    UNCONDITIONAL_FALSE = 15
    AND = 16
    OR = 17
    NOT_AND = 18
    NOT_OR = 19
    END_TARGET = 20
    TRUE_TARGET = 21
    FALSE_TARGET = 22


TYPE_PREFERENCE: list[list[int]] = [
    [3, 1],
    [3, 1],
    [3, 1],
    [3, 1],
    [1, 3],
    [1, 3],
    [1, 3],
    [1, 3],
    [3, 3],
    [3, 3],
    [3, 2],
    [2, 3],
    [0, 0],
    [0, 0],
    [3, 3],
    [3, 3],
    [3, 0],
    [3, 0],
    [0, 3],
    [0, 3],
]


@dataclass
class ConditionNode:
    type: ConditionNodeType
    node_label: int = INVALID_ID
    target_label: int = INVALID_ID
    target_node: Optional["ConditionNode"] = None
    has_alternate_target: bool = False
    incoming_nodes: int = 0
    inverted: bool = False
    expressions: Optional[list[Expression]] = None
    left_node: Optional["ConditionNode"] = None
    right_node: Optional["ConditionNode"] = None


class ConditionBuilder:
    def __init__(
        self,
        type_: ConditionBuilderType,
        ast: "Ast",
        end_target_label: int,
        true_target_label: int,
        false_target_label: int,
    ) -> None:
        self.ast = ast
        self.type = type_
        self.nodes: list[ConditionNode] = []
        self.condition_nodes: list[ConditionNode] = []
        self.end_assignment: Optional[ConditionNode] = None
        self.end_target: Optional[ConditionNode] = None
        self.true_target: Optional[ConditionNode] = None
        self.false_target: Optional[ConditionNode] = None
        if type_ == ConditionBuilderType.ASSIGNMENT:
            self.end_target = self.new_node(ConditionNodeType.END_TARGET)
            self.end_target.node_label = end_target_label
        self.true_target = self.new_node(ConditionNodeType.TRUE_TARGET)
        self.true_target.node_label = true_target_label
        self.false_target = self.new_node(ConditionNodeType.FALSE_TARGET)
        self.false_target.node_label = false_target_label

    def new_node(self, type_: ConditionNodeType) -> ConditionNode:
        node = ConditionNode(type_)
        self.nodes.append(node)
        return node

    @staticmethod
    def get_node_type(instruction: BC_OP, swapped: bool) -> ConditionNodeType:
        if instruction == BC_OP.BC_OP_ISLT:
            return ConditionNodeType.GREATER_THEN if swapped else ConditionNodeType.LESS_THAN
        if instruction == BC_OP.BC_OP_ISGE:
            return ConditionNodeType.NOT_GREATER_THEN if swapped else ConditionNodeType.NOT_LESS_THAN
        if instruction == BC_OP.BC_OP_ISLE:
            return ConditionNodeType.GREATER_EQUAL if swapped else ConditionNodeType.LESS_EQUAL
        if instruction == BC_OP.BC_OP_ISGT:
            return ConditionNodeType.NOT_GREATER_EQUAL if swapped else ConditionNodeType.NOT_LESS_EQUAL
        if instruction in (
            BC_OP.BC_OP_ISEQV,
            BC_OP.BC_OP_ISEQS,
            BC_OP.BC_OP_ISEQN,
            BC_OP.BC_OP_ISEQP,
        ):
            return ConditionNodeType.EQUAL
        if instruction in (
            BC_OP.BC_OP_ISNEV,
            BC_OP.BC_OP_ISNES,
            BC_OP.BC_OP_ISNEN,
            BC_OP.BC_OP_ISNEP,
        ):
            return ConditionNodeType.NOT_EQUAL
        if instruction in (BC_OP.BC_OP_ISTC, BC_OP.BC_OP_IST):
            return ConditionNodeType.TRUTHY_TEST
        if instruction in (BC_OP.BC_OP_ISFC, BC_OP.BC_OP_ISF):
            return ConditionNodeType.FALSY_TEST
        if instruction == BC_OP.BC_OP_JMP:
            return ConditionNodeType.UNCONDITIONAL_TRUE
        raise DecompilerError("Invalid condition node op")

    def add_node(
        self,
        type_: ConditionNodeType,
        node_label: int,
        target_label: int,
        expressions: Optional[list[Expression]],
        has_alternate_target: bool = False,
    ) -> None:
        node = self.new_node(type_)
        node.node_label = node_label
        node.target_label = target_label
        node.expressions = expressions
        node.has_alternate_target = has_alternate_target
        self.condition_nodes.append(node)

    def link_nodes(self) -> bool:
        if self.type == ConditionBuilderType.ASSIGNMENT:
            self.end_assignment = self.condition_nodes[-1]
            self.condition_nodes.append(self.false_target)
            self.condition_nodes.append(self.true_target)
            self.condition_nodes.append(self.end_target)
        else:
            self.condition_nodes.append(self.true_target)
            self.condition_nodes.append(self.false_target)
        for i in range(len(self.condition_nodes) - 1, -1, -1):
            node = self.condition_nodes[i]
            if node.target_label == INVALID_ID:
                continue
            for j in range(len(self.condition_nodes) - 1, -1, -1):
                if node.target_label != self.condition_nodes[j].node_label:
                    continue
                node.target_node = self.condition_nodes[j]
                self.condition_nodes[j].incoming_nodes += 1
                break
            if node.target_node is None:
                return False
        self.condition_nodes.pop()
        if self.type == ConditionBuilderType.ASSIGNMENT:
            self.condition_nodes.pop()
        return True

    def fix_return_nodes(self) -> None:
        for i in range(len(self.condition_nodes) - 2, -1, -1):
            node = self.condition_nodes[i]
            target_type = node.target_node.type
            if target_type == ConditionNodeType.END_TARGET:
                node.target_node = (
                    self.true_target
                    if node.type == ConditionNodeType.TRUTHY_TEST
                    else self.false_target
                )
                node.target_node.incoming_nodes += 1
                node.inverted = node.type == ConditionNodeType.FALSY_TEST
            elif target_type in (ConditionNodeType.TRUE_TARGET, ConditionNodeType.FALSE_TARGET):
                if target_type == ConditionNodeType.FALSE_TARGET:
                    node.inverted = True
                if self.type == ConditionBuilderType.ASSIGNMENT:
                    if node.type == ConditionNodeType.TRUTHY_TEST:
                        node.type = ConditionNodeType.BOOL_TRUTHY_TEST
                    elif node.type == ConditionNodeType.FALSY_TEST:
                        node.type = ConditionNodeType.BOOL_FALSY_TEST
            elif TYPE_PREFERENCE[node.type][int(node.inverted)] != 3:
                node.inverted = True

        if self.type != ConditionBuilderType.STATEMENT or self.condition_nodes[-2].inverted:
            return
        self.condition_nodes[-2].left_node = self.copy_node(self.condition_nodes[-2])
        self.condition_nodes[-2].right_node = self.new_node(ConditionNodeType.UNCONDITIONAL_FALSE)
        self.condition_nodes[-2].right_node.inverted = True
        self.condition_nodes[-2].target_node.incoming_nodes -= 1
        self.condition_nodes[-2].target_node = self.false_target
        self.condition_nodes[-2].target_node.incoming_nodes += 1
        self.condition_nodes[-2].type = ConditionNodeType.NOT_OR
        self.condition_nodes[-2].inverted = True

    @staticmethod
    def invert_any_node(left_node: ConditionNode, right_node: ConditionNode) -> bool:
        if left_node.target_node.type < ConditionNodeType.END_TARGET:
            if right_node.target_node.type < ConditionNodeType.END_TARGET:
                def calculate_score(node: ConditionNode) -> int:
                    if node.type in (
                        ConditionNodeType.AND,
                        ConditionNodeType.OR,
                        ConditionNodeType.NOT_AND,
                        ConditionNodeType.NOT_OR,
                    ):
                        return calculate_score(node.left_node) + calculate_score(node.right_node)
                    return (
                        TYPE_PREFERENCE[node.type][int(not node.inverted)]
                        - TYPE_PREFERENCE[node.type][int(node.inverted)]
                    )

                left_score = calculate_score(left_node)
                right_score = calculate_score(right_node)
                invert_left = (
                    left_score >= right_score if left_score > 0 else left_score > right_score
                )
                ConditionBuilder.invert_node(left_node if invert_left else right_node)
            else:
                ConditionBuilder.invert_node(left_node)
        else:
            if right_node.target_node.type > ConditionNodeType.END_TARGET:
                return False
            ConditionBuilder.invert_node(right_node)
        return True

    @staticmethod
    def invert_node(node: ConditionNode) -> None:
        node.inverted = not node.inverted
        if TYPE_PREFERENCE[node.type][int(node.inverted)] != 0:
            return
        ConditionBuilder.invert_node(node.left_node)
        ConditionBuilder.invert_node(node.right_node)
        if node.inverted:
            node.type = (
                ConditionNodeType.NOT_OR
                if node.type == ConditionNodeType.AND
                else ConditionNodeType.NOT_AND
            )
        else:
            node.type = (
                ConditionNodeType.OR
                if node.type == ConditionNodeType.NOT_AND
                else ConditionNodeType.AND
            )

    def copy_node(self, node: ConditionNode) -> ConditionNode:
        copy = self.new_node(node.type)
        copy.inverted = node.inverted
        copy.expressions = node.expressions
        copy.left_node = node.left_node
        copy.right_node = node.right_node
        return copy

    def merge_nodes(self, node: ConditionNode, target_node: ConditionNode) -> None:
        node.left_node = self.copy_node(node)
        node.right_node = target_node
        node.target_node.incoming_nodes -= 1
        node.target_node = target_node.target_node
        if not target_node.has_alternate_target:
            node.has_alternate_target = False
        node.inverted = target_node.inverted

    def build_boolean_logic(self) -> bool:
        # The final node is a target sentinel, not a condition to merge.
        i = len(self.condition_nodes) - 2
        while i > 0:
            prev = self.condition_nodes[i - 1]
            cur = self.condition_nodes[i]
            if cur.incoming_nodes == 0:
                if prev.target_node is cur.target_node:
                    if prev.inverted != cur.inverted and not self.invert_any_node(prev, cur):
                        return False
                    self.merge_nodes(prev, cur)
                    prev.type = ConditionNodeType.NOT_AND if prev.inverted else ConditionNodeType.OR
                    self.condition_nodes.pop(i)
                    i = len(self.condition_nodes) - 2
                    continue
                if prev.target_node is self.condition_nodes[i + 1]:
                    if prev.inverted == cur.inverted and not self.invert_any_node(prev, cur):
                        return False
                    self.merge_nodes(prev, cur)
                    prev.type = ConditionNodeType.NOT_OR if prev.inverted else ConditionNodeType.AND
                    self.condition_nodes.pop(i)
                    i = len(self.condition_nodes) - 2
                    continue
                if cur.target_node is self.condition_nodes[i + 1]:
                    if prev.inverted == cur.inverted:
                        self.invert_node(cur)
                    cur.left_node = self.copy_node(cur)
                    cur.right_node = self.new_node(ConditionNodeType.UNCONDITIONAL_FALSE)
                    cur.inverted = not cur.inverted
                    cur.right_node.inverted = cur.inverted
                    cur.type = ConditionNodeType.NOT_OR if cur.inverted else ConditionNodeType.AND
                    cur.target_node, prev.target_node = prev.target_node, cur.target_node
                    cur.has_alternate_target = prev.has_alternate_target
                    self.merge_nodes(prev, cur)
                    prev.type = ConditionNodeType.NOT_AND if prev.inverted else ConditionNodeType.OR
                    self.condition_nodes.pop(i)
                    i = len(self.condition_nodes) - 2
                    continue
                if cur.has_alternate_target and (
                    prev.target_node is self.end_assignment
                    or self.condition_nodes[i + 1] is self.end_assignment
                ):
                    cur.target_node.incoming_nodes -= 1
                    cur.target_node = self.end_assignment
                    self.end_assignment.incoming_nodes += 1
                    continue
                if cur.target_node is self.end_assignment and prev.has_alternate_target:
                    prev.target_node.incoming_nodes -= 1
                    prev.target_node = self.end_assignment
                    self.end_assignment.incoming_nodes += 1
                    continue
            elif cur.incoming_nodes == 1 and prev.target_node is cur:
                prev.left_node = self.copy_node(prev)
                prev.right_node = self.new_node(ConditionNodeType.UNCONDITIONAL_FALSE)
                prev.inverted = not prev.inverted
                prev.right_node.inverted = prev.inverted
                prev.type = ConditionNodeType.NOT_OR if prev.inverted else ConditionNodeType.AND
                prev.has_alternate_target = cur.has_alternate_target
                same_inversion = prev.inverted == cur.inverted
                self.merge_nodes(prev, cur)
                if same_inversion:
                    prev.type = ConditionNodeType.NOT_AND if prev.inverted else ConditionNodeType.OR
                else:
                    prev.type = ConditionNodeType.NOT_OR if prev.inverted else ConditionNodeType.AND
                self.condition_nodes.pop(i)
                i = len(self.condition_nodes) - 2
                continue
            i -= 1
        self.condition_nodes.pop()
        return len(self.condition_nodes) == 1

    def build_not(self, operand: Expression) -> Expression:
        expression = self.ast.new_expression(AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION)
        expression.unary_operation.type = AST_UNARY_OPERATION.AST_UNARY_NOT
        expression.unary_operation.operand = operand
        return expression

    def build_binary(
        self, type_: ConditionNodeType, left_operand: Expression, right_operand: Expression
    ) -> Expression:
        expression = self.ast.new_expression(AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION)
        if type_ in (ConditionNodeType.LESS_THAN, ConditionNodeType.NOT_LESS_THAN):
            expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_LESS_THAN
        elif type_ in (ConditionNodeType.LESS_EQUAL, ConditionNodeType.NOT_LESS_EQUAL):
            expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_LESS_EQUAL
        elif type_ in (ConditionNodeType.GREATER_THEN, ConditionNodeType.NOT_GREATER_THEN):
            expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_GREATER_THEN
        elif type_ in (ConditionNodeType.GREATER_EQUAL, ConditionNodeType.NOT_GREATER_EQUAL):
            expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_GREATER_EQUAL
        elif type_ == ConditionNodeType.EQUAL:
            expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_EQUAL
        elif type_ == ConditionNodeType.NOT_EQUAL:
            expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_NOT_EQUAL
        elif type_ in (ConditionNodeType.AND, ConditionNodeType.NOT_AND):
            expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_AND
        elif type_ in (ConditionNodeType.OR, ConditionNodeType.NOT_OR):
            expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_OR
        else:
            raise DecompilerError("Invalid condition binary op")
        expression.binary_operation.left_operand = left_operand
        expression.binary_operation.right_operand = right_operand
        return expression

    def build_expression(self, node: ConditionNode) -> Expression:
        if node.type in (
            ConditionNodeType.LESS_THAN,
            ConditionNodeType.LESS_EQUAL,
            ConditionNodeType.GREATER_THEN,
            ConditionNodeType.GREATER_EQUAL,
        ):
            expr = self.build_binary(node.type, node.expressions[0], node.expressions[1])
            return self.build_not(expr) if node.inverted else expr
        if node.type in (
            ConditionNodeType.NOT_LESS_THAN,
            ConditionNodeType.NOT_LESS_EQUAL,
            ConditionNodeType.NOT_GREATER_THEN,
            ConditionNodeType.NOT_GREATER_EQUAL,
        ):
            expr = self.build_binary(node.type, node.expressions[0], node.expressions[1])
            return expr if node.inverted else self.build_not(expr)
        if node.type == ConditionNodeType.EQUAL:
            return self.build_binary(
                ConditionNodeType.NOT_EQUAL if node.inverted else ConditionNodeType.EQUAL,
                node.expressions[0],
                node.expressions[1],
            )
        if node.type == ConditionNodeType.NOT_EQUAL:
            return self.build_binary(
                ConditionNodeType.EQUAL if node.inverted else ConditionNodeType.NOT_EQUAL,
                node.expressions[0],
                node.expressions[1],
            )
        if node.type == ConditionNodeType.TRUTHY_TEST:
            return self.build_not(node.expressions[-1]) if node.inverted else node.expressions[-1]
        if node.type == ConditionNodeType.FALSY_TEST:
            return node.expressions[-1] if node.inverted else self.build_not(node.expressions[-1])
        if node.type == ConditionNodeType.BOOL_TRUTHY_TEST:
            return (
                self.build_not(node.expressions[-1])
                if node.inverted
                else self.build_not(self.build_not(node.expressions[-1]))
            )
        if node.type == ConditionNodeType.BOOL_FALSY_TEST:
            return (
                self.build_not(self.build_not(node.expressions[-1]))
                if node.inverted
                else self.build_not(node.expressions[-1])
            )
        if node.type == ConditionNodeType.UNCONDITIONAL_TRUE:
            return self.ast.new_primitive(1 if node.inverted else 2)
        if node.type == ConditionNodeType.UNCONDITIONAL_FALSE:
            return self.ast.new_primitive(2 if node.inverted else 1)
        if node.type in (ConditionNodeType.AND, ConditionNodeType.OR):
            expr = self.build_binary(
                node.type, self.build_expression(node.left_node), self.build_expression(node.right_node)
            )
            return self.build_not(expr) if node.inverted else expr
        if node.type in (ConditionNodeType.NOT_AND, ConditionNodeType.NOT_OR):
            expr = self.build_binary(
                node.type, self.build_expression(node.left_node), self.build_expression(node.right_node)
            )
            return expr if node.inverted else self.build_not(expr)
        raise DecompilerError("Invalid condition expression node")

    def build_condition(self) -> Optional[Expression]:
        if self.link_nodes():
            self.fix_return_nodes()
            if self.build_boolean_logic():
                return self.build_expression(self.condition_nodes[-1])
        return None


class Ast:
    def __init__(
        self,
        bytecode: Bytecode,
        ignore_debug_info: bool,
        minimize_diffs: bool,
        format_arg: str,
        format_label: str,
        format_iter: str,
        format_var: str,
    ) -> None:
        self.bytecode = bytecode
        self.ignore_debug_info = ignore_debug_info
        self.minimize_diffs = minimize_diffs
        self.format_arg = format_arg
        self.format_label = format_label
        self.format_iter = format_iter
        self.format_var = format_var
        self.is_fr2_enabled = False
        self.chunk: Optional[Function] = None
        self.statements: list[Statement] = []
        self.functions: list[Function] = []
        self.expressions: list[Expression] = []
        self.prototype_data_left = 0

    def _function_name_key(self, function: Function) -> int:
        return function.level if self.minimize_diffs else function.id

    def _format_arg_name(self, function: Function, index: int) -> str:
        return format_generated_name(
            self.format_arg,
            self._function_name_key(function),
            index,
            "arg",
            self.bytecode.file_path,
            "Ast::_format_arg_name",
        )

    def _format_label_name(self, function: Function, counter: int) -> str:
        return format_generated_name(
            self.format_label,
            self._function_name_key(function),
            counter,
            "label",
            self.bytecode.file_path,
            "Ast::_format_label_name",
        )

    def _format_iter_name(self, function: Function, counter: int) -> str:
        return format_generated_name(
            self.format_iter,
            self._function_name_key(function),
            counter,
            "iter",
            self.bytecode.file_path,
            "Ast::_format_iter_name",
        )

    def _format_var_name(self, function: Function, counter: int) -> str:
        return format_generated_name(
            self.format_var,
            self._function_name_key(function),
            counter,
            "var",
            self.bytecode.file_path,
            "Ast::_format_var_name",
        )

    def new_function(self, prototype: Prototype, level: int) -> Function:
        function = Function(prototype, level, self.ignore_debug_info)
        self.functions.append(function)
        return function

    def new_statement(self, type_: AST_STATEMENT) -> Statement:
        statement = Statement(type_)
        self.statements.append(statement)
        return statement

    def new_expression(self, type_: AST_EXPRESSION) -> Expression:
        expression = Expression(type_)
        self.expressions.append(expression)
        return expression

    def __call__(self) -> None:
        # Run reconstruction passes in their established order.
        self.chunk = self.new_function(self.bytecode.main, 0)
        self.is_fr2_enabled = (
            self.bytecode.header_version == BC_VERSION_2
            and bool(self.bytecode.header_flags & BC_F_FR2)
        )
        self.prototype_data_left = self.bytecode.prototypes_total_size
        verbose_log(
            f"AST pipeline start (FR2={'on' if self.is_fr2_enabled else 'off'})"
        )
        function_counter = 0
        self.build_functions(self.chunk, function_counter)
        verbose_log("AST pipeline complete")

    @staticmethod
    def _debug_block_snapshot(block: list[Statement]) -> str:
        parts: list[str] = []
        for idx, statement in enumerate(block):
            op_name = (
                statement.instruction.type.name
                if statement.instruction.type is not None
                else "NONE"
            )
            extras: list[str] = []
            if statement.assignment.variables:
                variable = statement.assignment.variables[-1]
                if variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    extras.append(f"slot={variable.slot}")
            if statement.assignment.expressions:
                expression = statement.assignment.expressions[-1]
                if expression.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT:
                    extras.append(f"const={expression.constant.type.name}")
            parts.append(
                (
                    f"{idx}:{statement.type.name}"
                    f"/op={op_name}"
                    f"/id={statement.instruction.id}"
                    f"/target={statement.instruction.target}"
                    f"/label={statement.instruction.label}"
                    f"/vars={len(statement.assignment.variables)}"
                    f"/exprs={len(statement.assignment.expressions)}"
                    + ("/" + ",".join(extras) if extras else "")
                )
            )
        return "; ".join(parts)

    # --- AST reconstruction passes ---
    def build_functions(self, function: Function, function_counter: int) -> int:
        initial_id = function_counter
        verbose_push(f"Build function[{initial_id}] level={function.level}")
        function.id = function_counter
        function_counter += 1
        verbose_log("Pass: build_instructions")
        self.build_instructions(function)
        if not function.has_debug_info:
            verbose_log("Pass: build_upvalue_scopes")
            function.slot_scope_collector.build_upvalue_scopes()
        verbose_log("Pass: build_slot_scopes")
        self.build_slot_scopes(function, function.block, None)
        verbose_log("Pass: assert_scopes_closed")
        decompiler_assert(
            function.slot_scope_collector.assert_scopes_closed(),
            "Failed to close slot scopes",
            self.bytecode.file_path,
            "Ast::build_functions",
            __file__,
            0,
        )
        verbose_log("Pass: eliminate_slots")
        self.eliminate_slots(function, function.block, None)
        if _verbose_enabled and function.level == 1 and function.id == 42:
            verbose_log(
                "Debug function[42] snapshot after eliminate_slots: "
                + self._debug_block_snapshot(function.block)
            )
            label_parts: list[str] = []
            for label_index, label in enumerate(function.labels):
                label_parts.append(
                    f"{label_index}:target={label.target},jumps={label.jump_ids}"
                )
            verbose_log("Debug function[42] labels after eliminate_slots: " + "; ".join(label_parts))
        verbose_log("Pass: eliminate_conditions")
        self.eliminate_conditions(function, function.block, None)
        if _verbose_enabled and function.level == 1 and function.id == 42:
            verbose_log(
                "Debug function[42] snapshot after eliminate_conditions: "
                + self._debug_block_snapshot(function.block)
            )
            label_parts = []
            for label_index, label in enumerate(function.labels):
                label_parts.append(
                    f"{label_index}:target={label.target},jumps={label.jump_ids}"
                )
            verbose_log("Debug function[42] labels after eliminate_conditions: " + "; ".join(label_parts))
        verbose_log("Pass: build_if_statements")
        self.build_if_statements(function, function.block, None)
        verbose_log("Pass: clean_up")
        self.clean_up(function)
        self.prototype_data_left -= function.prototype.prototype_size
        print_progress_bar(
            self.bytecode.prototypes_total_size - self.prototype_data_left,
            self.bytecode.prototypes_total_size,
        )

        for i in range(len(function.child_functions) - 1, -1, -1):
            function_counter = self.build_functions(function.child_functions[i], function_counter)
        verbose_pop(f"Function[{initial_id}] build complete")
        return function_counter

    def build_instructions(self, function: Function) -> None:
        upvalues: list[int] = []
        function.block = [
            self.new_statement(AST_STATEMENT.AST_STATEMENT_INSTRUCTION)
            for _ in function.prototype.instructions
        ]

        for i in range(len(function.block) - 1, -1, -1):
            statement = function.block[i]
            instruction = function.prototype.instructions[i]
            statement.instruction.type = instruction.type
            statement.instruction.a = instruction.a
            statement.instruction.b = instruction.b
            statement.instruction.c = instruction.c
            statement.instruction.d = instruction.d
            statement.instruction.id = i

            itype = statement.instruction.type
            if itype == BC_OP.BC_OP_FNEW:
                child = self.new_function(
                    function.get_constant(statement.instruction.d).prototype,
                    function.level + 1,
                )
                statement.function = child
                function.child_functions.append(child)
                child.upvalues = [FunctionUpvalue() for _ in child.prototype.upvalues]
                for j in range(len(child.upvalues) - 1, -1, -1):
                    child.upvalues[j].slot = child.prototype.upvalues[j] & 0xFF
                    if not (child.prototype.upvalues[j] & BC_UV_LOCAL):
                        child.upvalues[j].slot_scope = function.upvalues[child.upvalues[j].slot].slot_scope
                        continue
                    child.upvalues[j].local = True
                    if child.upvalues[j].slot >= function.prototype.header.parameters:
                        upvalues.append(child.upvalues[j].slot)
                if upvalues:
                    function.slot_scope_collector.add_upvalues(statement.instruction.id, upvalues)
                    upvalues.clear()
                continue

            if itype in (
                BC_OP.BC_OP_CALLMT,
                BC_OP.BC_OP_CALLT,
                BC_OP.BC_OP_RETM,
                BC_OP.BC_OP_RET,
                BC_OP.BC_OP_RET0,
                BC_OP.BC_OP_RET1,
            ):
                statement.type = AST_STATEMENT.AST_STATEMENT_RETURN
                continue

            if itype in (
                BC_OP.BC_OP_UCLO,
                BC_OP.BC_OP_ISNEXT,
                BC_OP.BC_OP_FORI,
                BC_OP.BC_OP_FORL,
                BC_OP.BC_OP_ITERL,
                BC_OP.BC_OP_LOOP,
                BC_OP.BC_OP_JMP,
            ):
                statement.instruction.target = (
                    statement.instruction.id + (statement.instruction.d - BC_OP_JMP_BIAS + 1)
                )
                continue

        self.assign_debug_info(function)

    def assign_debug_info(self, function: Function) -> None:
        if not function.has_debug_info:
            self.group_jumps(function)
            return

        active_local_scopes: list[int] = []
        function.parameter_names = [""] * function.prototype.header.parameters
        for i in range(len(function.parameter_names) - 1, -1, -1):
            function.parameter_names[i] = function.prototype.variable_infos[i].name
            active_local_scopes.append(function.prototype.variable_infos[i].scope_end)

        for i in range(len(function.parameter_names), len(function.prototype.variable_infos)):
            info = function.prototype.variable_infos[i]
            decompiler_assert(
                (not active_local_scopes)
                or info.scope_begin >= active_local_scopes[-1]
                or info.scope_end <= active_local_scopes[-1],
                "Illegal variable scope border overlap",
                self.bytecode.file_path,
                "Ast::assign_debug_info",
                __file__,
                0,
            )

            while active_local_scopes and info.scope_end > active_local_scopes[-1]:
                active_local_scopes.pop()

            if info.type != BC_VAR.BC_VAR_STR:
                active_local_scopes.append(info.scope_end)
                continue

            if (
                function.locals
                and info.scope_begin == info.scope_end
                and function.locals[-1].scope_end == info.scope_end
            ):
                index = Ast.get_block_index_from_id(function.block, info.scope_begin)
                if index != INVALID_ID:
                    statement = function.block[index]
                    valid_kpri_knil = False
                    if statement.instruction.type == BC_OP.BC_OP_KPRI:
                        if statement.instruction.d == 0:
                            valid_kpri_knil = True
                    elif statement.instruction.type == BC_OP.BC_OP_KNIL:
                        valid_kpri_knil = True
                    if valid_kpri_knil:
                        a_or_d = (
                            statement.instruction.a
                            if statement.instruction.type == BC_OP.BC_OP_KPRI
                            else statement.instruction.d
                        )
                        if a_or_d < len(active_local_scopes):
                            while len(active_local_scopes) != function.locals[-1].base_slot:
                                decompiler_assert(
                                    bool(active_local_scopes)
                                    and active_local_scopes[-1] == info.scope_end,
                                    "Unable to build variable scope",
                                    self.bytecode.file_path,
                                    "Ast::assign_debug_info",
                                    __file__,
                                    0,
                                )
                                active_local_scopes.pop()

                            prev_exclude = False
                            if len(function.locals) >= 1:
                                prev = function.locals[-1]
                                prev_exclude = (
                                    prev.exclude_block
                                    if prev.scope_begin == prev.scope_end
                                    else True
                                )
                            local = Local(
                                base_slot=len(active_local_scopes),
                                scope_begin=info.scope_begin,
                                scope_end=info.scope_end,
                                exclude_block=prev_exclude,
                            )
                            function.locals.append(local)
                            function.add_jump(local.scope_begin, local.scope_end + 1)

            if (
                not function.locals
                or info.scope_begin != function.locals[-1].scope_begin
                or info.scope_end != function.locals[-1].scope_end
            ):
                local = Local(
                    base_slot=len(active_local_scopes),
                    scope_begin=info.scope_begin,
                    scope_end=info.scope_end,
                )
                function.locals.append(local)
                function.add_jump(local.scope_begin, local.scope_end + 1)

            function.locals[-1].names.append(info.name)
            active_local_scopes.append(function.locals[-1].scope_end)

        self.group_jumps(function)

    def group_jumps(self, function: Function) -> None:
        i = len(function.block) - 1
        while i >= 0:
            statement = function.block[i]
            itype = statement.instruction.type
            if itype in (BC_OP.BC_OP_ISTC, BC_OP.BC_OP_ISFC):
                function.add_jump(statement.instruction.id, statement.instruction.id + 2)

            if itype in (
                BC_OP.BC_OP_ISTC,
                BC_OP.BC_OP_ISFC,
                BC_OP.BC_OP_ISLT,
                BC_OP.BC_OP_ISGE,
                BC_OP.BC_OP_ISLE,
                BC_OP.BC_OP_ISGT,
                BC_OP.BC_OP_ISEQV,
                BC_OP.BC_OP_ISNEV,
                BC_OP.BC_OP_ISEQS,
                BC_OP.BC_OP_ISNES,
                BC_OP.BC_OP_ISEQN,
                BC_OP.BC_OP_ISNEN,
                BC_OP.BC_OP_ISEQP,
                BC_OP.BC_OP_ISNEP,
                BC_OP.BC_OP_IST,
                BC_OP.BC_OP_ISF,
            ):
                statement.type = AST_STATEMENT.AST_STATEMENT_CONDITION
                statement.instruction.target = function.block[i + 1].instruction.target
                function.block.pop(i + 1)
                function.slot_scope_collector.add_jump(
                    statement.instruction.id + 1, statement.instruction.target
                )
                i -= 1
                continue

            if itype == BC_OP.BC_OP_UCLO:
                function.slot_scope_collector.add_upvalue_close(
                    statement.instruction.id,
                    statement.instruction.target,
                    statement.instruction.a,
                )
            if itype in (BC_OP.BC_OP_UCLO, BC_OP.BC_OP_JMP):
                statement.type = AST_STATEMENT.AST_STATEMENT_GOTO
            if itype in (BC_OP.BC_OP_UCLO, BC_OP.BC_OP_JMP, BC_OP.BC_OP_LOOP):
                function.add_jump(statement.instruction.id, statement.instruction.target)
            i -= 1

        for i in range(len(function.block) - 1, -1, -1):
            statement = function.block[i]
            statement.instruction.label = function.get_label_from_id(statement.instruction.id)
            itype = statement.instruction.type

            if itype == BC_OP.BC_OP_UCLO:
                if (
                    statement.instruction.d == BC_OP_JMP_BIAS
                    or (
                        i + 1 < len(function.block)
                        and statement.instruction.target
                        == Ast.get_extended_id_from_statement(function.block[i + 1])
                    )
                ):
                    statement.type = AST_STATEMENT.AST_STATEMENT_EMPTY
                    function.remove_jump(statement.instruction.id, statement.instruction.target)
                continue

            if itype == BC_OP.BC_OP_ITERC:
                if statement.instruction.label != INVALID_ID:
                    index = Ast.get_block_index_from_id(
                        function.block,
                        function.labels[statement.instruction.label].jump_ids[0],
                    )
                    if index != INVALID_ID:
                        function.block[index].type = AST_STATEMENT.AST_STATEMENT_INSTRUCTION
                        function.remove_jump(
                            function.block[index].instruction.id,
                            function.block[index].instruction.target,
                        )
                continue

            if itype == BC_OP.BC_OP_JMP:
                if statement.type != AST_STATEMENT.AST_STATEMENT_GOTO:
                    continue
                function.slot_scope_collector.add_jump(
                    statement.instruction.id, statement.instruction.target
                )
                if (
                    statement.instruction.target == statement.instruction.id
                    or i == 0
                    or function.block[i - 1].instruction.type != BC_OP.BC_OP_JMP
                    or function.block[i - 1].instruction.d != BC_OP_JMP_BIAS
                    or len(function.labels[statement.instruction.label].jump_ids) > 1
                ):
                    continue
                function.remove_jump(
                    function.block[i - 1].instruction.id,
                    function.block[i - 1].instruction.target,
                )
                function.block[i - 1].type = AST_STATEMENT.AST_STATEMENT_CONDITION
                function.block[i - 1].instruction.target = statement.instruction.target
                function.block.pop(i)
                continue

        for i in range(len(function.locals) - 1, -1, -1):
            function.remove_jump(function.locals[i].scope_begin, function.locals[i].scope_end + 1)

        for i in range(len(function.block) - 1, -1, -1):
            if (
                i > 0
                and function.block[i].type == AST_STATEMENT.AST_STATEMENT_RETURN
                and function.block[i - 1].type == AST_STATEMENT.AST_STATEMENT_RETURN
                and function.is_valid_label(function.block[i].instruction.label)
                and len(function.labels[function.block[i].instruction.label].jump_ids) == 1
            ):
                index = Ast.get_block_index_from_id(
                    function.block,
                    function.labels[function.block[i].instruction.label].jump_ids[-1],
                )
                if (
                    index != INVALID_ID
                    and function.block[index].type == AST_STATEMENT.AST_STATEMENT_GOTO
                    and function.block[index].instruction.type == BC_OP.BC_OP_UCLO
                ):
                    function.remove_jump(
                        function.block[index].instruction.id,
                        function.block[index].instruction.target,
                    )
                    function.block[index].type = AST_STATEMENT.AST_STATEMENT_RETURN
                    function.block[index].instruction.type = function.block[i].instruction.type
                    function.block[index].instruction.a = function.block[i].instruction.a
                    function.block[index].instruction.b = function.block[i].instruction.b
                    function.block[index].instruction.c = function.block[i].instruction.c
                    function.block[index].instruction.d = function.block[i].instruction.d
                    function.block[i].type = AST_STATEMENT.AST_STATEMENT_EMPTY
                    continue
            if function.block[i].instruction.type == BC_OP.BC_OP_RET0:
                function.block[i].type = AST_STATEMENT.AST_STATEMENT_EMPTY
            break

        self.build_loops(function)

    def build_loops(self, function: Function) -> None:
        def build_break_statements(block: list[Statement], break_target: int) -> None:
            for j in range(len(block) - 1, -1, -1):
                if (
                    block[j].type == AST_STATEMENT.AST_STATEMENT_GOTO
                    and block[j].instruction.target == break_target
                ):
                    block[j].type = AST_STATEMENT.AST_STATEMENT_BREAK

        i = len(function.block) - 1
        while i >= 0:
            if function.block[i].type != AST_STATEMENT.AST_STATEMENT_INSTRUCTION:
                i -= 1
                continue

            itype = function.block[i].instruction.type
            if itype in (BC_OP.BC_OP_ISNEXT, BC_OP.BC_OP_JMP):
                function.block[i].type = AST_STATEMENT.AST_STATEMENT_GENERIC_FOR
                target_index = Ast.get_block_index_from_id(
                    function.block, function.block[i].instruction.target
                )
                decompiler_assert(
                    target_index != INVALID_ID and target_index + 2 < len(function.block),
                    "Invalid generic for loop target",
                    self.bytecode.file_path,
                    "Ast::build_loops",
                    __file__,
                    0,
                )
                break_target = Ast.get_extended_id_from_statement(function.block[target_index + 2])
                function.block[target_index].instruction.target = function.block[i].instruction.label
                function.block[i].instruction = StatementInstruction(
                    type=function.block[target_index].instruction.type,
                    a=function.block[target_index].instruction.a,
                    b=function.block[target_index].instruction.b,
                    c=function.block[target_index].instruction.c,
                    d=function.block[target_index].instruction.d,
                    id=function.block[target_index + 1].instruction.target - 1,
                    target=function.block[target_index + 1].instruction.id + 1,
                    label=function.block[target_index].instruction.target,
                )
                function.block[target_index].type = AST_STATEMENT.AST_STATEMENT_EMPTY
                function.block[i].block = list(function.block[i + 1 : target_index + 1])
                del function.block[i + 1 : target_index + 2]
                function.slot_scope_collector.add_loop(
                    function.block[i].instruction.id, function.block[i].instruction.target
                )
                build_break_statements(function.block[i].block, break_target)
                self.build_local_scopes(function, function.block[i].block)
                i -= 1
                continue

            if itype == BC_OP.BC_OP_FORI:
                function.block[i].type = AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR
                target_index = Ast.get_block_index_from_id(
                    function.block, function.block[i].instruction.target
                )
                decompiler_assert(
                    target_index != INVALID_ID and target_index > 0,
                    "Invalid numeric for loop target",
                    self.bytecode.file_path,
                    "Ast::build_loops",
                    __file__,
                    0,
                )
                break_target = Ast.get_extended_id_from_statement(function.block[target_index])
                function.block[target_index - 1].type = AST_STATEMENT.AST_STATEMENT_EMPTY
                function.block[i].block = list(function.block[i + 1 : target_index])
                del function.block[i + 1 : target_index]
                function.slot_scope_collector.add_loop(
                    function.block[i].instruction.id, function.block[i].instruction.target
                )
                build_break_statements(function.block[i].block, break_target)
                self.build_local_scopes(function, function.block[i].block)
                i -= 1
                continue

            if itype == BC_OP.BC_OP_LOOP:
                decompiler_assert(
                    function.block[i].instruction.target >= function.block[i].instruction.id,
                    "LOOP instruction has invalid jump target",
                    self.bytecode.file_path,
                    "Ast::build_loops",
                    __file__,
                    0,
                )
                function.remove_jump(
                    function.block[i].instruction.id, function.block[i].instruction.target
                )
                if function.block[i].instruction.target == function.block[i].instruction.id:
                    decompiler_assert(
                        i + 1 < len(function.block)
                        and function.block[i + 1].type == AST_STATEMENT.AST_STATEMENT_GOTO
                        and function.block[i + 1].instruction.target <= function.block[i].instruction.id
                        and not function.is_valid_label(function.block[i + 1].instruction.label),
                        "Invalid goto loop",
                        self.bytecode.file_path,
                        "Ast::build_loops",
                        __file__,
                        0,
                    )
                    function.block[i].type = AST_STATEMENT.AST_STATEMENT_EMPTY
                    function.block[i + 1].instruction.type = function.block[i].instruction.type
                    i -= 1
                    continue

                function.block[i].type = AST_STATEMENT.AST_STATEMENT_LOOP
                target_index = Ast.get_block_index_from_id(
                    function.block, function.block[i].instruction.target
                )
                decompiler_assert(
                    target_index != INVALID_ID,
                    "Invalid loop target",
                    self.bytecode.file_path,
                    "Ast::build_loops",
                    __file__,
                    0,
                )
                break_target = Ast.get_extended_id_from_statement(function.block[target_index])
                function.block[i].block = list(function.block[i + 1 : target_index])
                del function.block[i + 1 : target_index]
                function.slot_scope_collector.add_loop(
                    function.block[i].instruction.id, function.block[i].instruction.target
                )
                build_break_statements(function.block[i].block, break_target)

                if (
                    function.block[i].block
                    and function.block[i].block[-1].type == AST_STATEMENT.AST_STATEMENT_CONDITION
                    and function.is_valid_label(function.block[i].instruction.label)
                    and break_target != function.block[i].instruction.id
                ):
                    jump_ids = function.labels[function.block[i].instruction.label].jump_ids
                    for j in range(len(jump_ids) - 1, -1, -1):
                        if jump_ids[j] <= function.block[i].instruction.id:
                            break
                        if jump_ids[j] >= function.block[i].instruction.target:
                            continue
                        target_index = Ast.get_block_index_from_id(
                            function.block[i].block, jump_ids[j] - 1
                        )
                        if (
                            target_index != INVALID_ID
                            and function.block[i].block[target_index].type
                            == AST_STATEMENT.AST_STATEMENT_CONDITION
                        ):
                            brk = self.new_statement(AST_STATEMENT.AST_STATEMENT_BREAK)
                            brk.instruction.type = BC_OP.BC_OP_JMP
                            brk.instruction.target = break_target
                            function.block[i].block.append(brk)
                            goto = self.new_statement(AST_STATEMENT.AST_STATEMENT_GOTO)
                            goto.instruction.type = BC_OP.BC_OP_JMP
                            goto.instruction.target = function.block[i].instruction.id
                            function.block[i].block.append(goto)
                        break

                self.build_local_scopes(function, function.block[i].block)
                i -= 1
                continue

            i -= 1

        self.build_local_scopes(function, function.block)

    def build_local_scopes(self, function: Function, block: list[Statement]) -> None:
        if not function.has_debug_info:
            self.build_expressions(function, block)
            return

        for i in range(len(function.locals) - 1, -1, -1):
            scope_begin_index = Ast.get_block_index_from_id(block, function.locals[i].scope_begin)
            if scope_begin_index == INVALID_ID:
                continue
            if block[scope_begin_index].type in (
                AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR,
                AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
            ):
                block[scope_begin_index].locals = function.locals[i]
                continue

            scope_begin_index += 1
            declaration = self.new_statement(AST_STATEMENT.AST_STATEMENT_DECLARATION)
            declaration.locals = function.locals[i]
            block.insert(scope_begin_index, declaration)

            if function.locals[i].scope_end > function.locals[i].scope_begin:
                block[scope_begin_index].instruction.id = function.locals[i].scope_begin + 1
                scope_end_index = Ast.get_block_index_from_id(
                    block, function.locals[i].scope_end + 1
                )
                if scope_end_index == INVALID_ID:
                    scope_end_index = len(block)
                while (
                    scope_end_index > 0
                    and block[scope_end_index - 1].type
                    == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and block[scope_end_index - 1].locals is not None
                    and block[scope_end_index - 1].locals.exclude_block
                ):
                    scope_end_index -= 1

                block[scope_begin_index].block = list(
                    block[scope_begin_index + 1 : scope_end_index]
                )
                del block[scope_begin_index + 1 : scope_end_index]
                self.build_expressions(function, block[scope_begin_index].block)

        self.build_expressions(function, block)

    def build_expressions(self, function: Function, block: list[Statement]) -> None:
        i = len(block) - 1
        while i >= 0:
            if block[i].type == AST_STATEMENT.AST_STATEMENT_INSTRUCTION:
                statement = block[i]
                statement.type = AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                statement.assignment.expressions = [None]  # type: ignore[list-item]
                itype = statement.instruction.type

                if itype == BC_OP.BC_OP_MOV:
                    expr = self.new_slot(statement.instruction.d)
                    statement.assignment.expressions[-1] = expr
                    statement.assignment.register_slots(expr)
                    statement.assignment.variables = [
                        AstVariable(type=AST_VARIABLE.AST_VARIABLE_SLOT, slot=statement.instruction.a)
                    ]
                    i -= 1
                    continue

                if itype in (BC_OP.BC_OP_NOT, BC_OP.BC_OP_UNM, BC_OP.BC_OP_LEN):
                    expr = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION)
                    if itype == BC_OP.BC_OP_NOT:
                        expr.unary_operation.type = AST_UNARY_OPERATION.AST_UNARY_NOT
                        statement.assignment.allowed_constant_type = CONSTANT_TYPE.INVALID_CONSTANT
                    elif itype == BC_OP.BC_OP_UNM:
                        expr.unary_operation.type = AST_UNARY_OPERATION.AST_UNARY_MINUS
                        statement.assignment.allowed_constant_type = CONSTANT_TYPE.BOOL_CONSTANT
                    else:
                        expr.unary_operation.type = AST_UNARY_OPERATION.AST_UNARY_LENGTH
                    expr.unary_operation.operand = self.new_slot(statement.instruction.d)
                    statement.assignment.register_slots(expr.unary_operation.operand)
                    statement.assignment.expressions[-1] = expr
                    statement.assignment.variables = [
                        AstVariable(type=AST_VARIABLE.AST_VARIABLE_SLOT, slot=statement.instruction.a)
                    ]
                    i -= 1
                    continue

                if itype in (
                    BC_OP.BC_OP_ADDVN,
                    BC_OP.BC_OP_SUBVN,
                    BC_OP.BC_OP_MULVN,
                    BC_OP.BC_OP_DIVVN,
                    BC_OP.BC_OP_MODVN,
                    BC_OP.BC_OP_ADDNV,
                    BC_OP.BC_OP_SUBNV,
                    BC_OP.BC_OP_MULNV,
                    BC_OP.BC_OP_DIVNV,
                    BC_OP.BC_OP_MODNV,
                    BC_OP.BC_OP_ADDVV,
                    BC_OP.BC_OP_SUBVV,
                    BC_OP.BC_OP_MULVV,
                    BC_OP.BC_OP_DIVVV,
                    BC_OP.BC_OP_MODVV,
                    BC_OP.BC_OP_POW,
                    BC_OP.BC_OP_CAT,
                ):
                    if itype != BC_OP.BC_OP_CAT:
                        statement.assignment.allowed_constant_type = CONSTANT_TYPE.BOOL_CONSTANT
                    expr = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION)
                    op_map = {
                        BC_OP.BC_OP_ADDVN: AST_BINARY_OPERATION.AST_BINARY_ADDITION,
                        BC_OP.BC_OP_ADDNV: AST_BINARY_OPERATION.AST_BINARY_ADDITION,
                        BC_OP.BC_OP_ADDVV: AST_BINARY_OPERATION.AST_BINARY_ADDITION,
                        BC_OP.BC_OP_SUBVN: AST_BINARY_OPERATION.AST_BINARY_SUBTRACTION,
                        BC_OP.BC_OP_SUBNV: AST_BINARY_OPERATION.AST_BINARY_SUBTRACTION,
                        BC_OP.BC_OP_SUBVV: AST_BINARY_OPERATION.AST_BINARY_SUBTRACTION,
                        BC_OP.BC_OP_MULVN: AST_BINARY_OPERATION.AST_BINARY_MULTIPLICATION,
                        BC_OP.BC_OP_MULNV: AST_BINARY_OPERATION.AST_BINARY_MULTIPLICATION,
                        BC_OP.BC_OP_MULVV: AST_BINARY_OPERATION.AST_BINARY_MULTIPLICATION,
                        BC_OP.BC_OP_DIVVN: AST_BINARY_OPERATION.AST_BINARY_DIVISION,
                        BC_OP.BC_OP_DIVNV: AST_BINARY_OPERATION.AST_BINARY_DIVISION,
                        BC_OP.BC_OP_DIVVV: AST_BINARY_OPERATION.AST_BINARY_DIVISION,
                        BC_OP.BC_OP_MODVN: AST_BINARY_OPERATION.AST_BINARY_MODULO,
                        BC_OP.BC_OP_MODNV: AST_BINARY_OPERATION.AST_BINARY_MODULO,
                        BC_OP.BC_OP_MODVV: AST_BINARY_OPERATION.AST_BINARY_MODULO,
                        BC_OP.BC_OP_POW: AST_BINARY_OPERATION.AST_BINARY_EXPONENTATION,
                        BC_OP.BC_OP_CAT: AST_BINARY_OPERATION.AST_BINARY_CONCATENATION,
                    }
                    expr.binary_operation.type = op_map[itype]

                    if itype in (
                        BC_OP.BC_OP_ADDVN,
                        BC_OP.BC_OP_SUBVN,
                        BC_OP.BC_OP_MULVN,
                        BC_OP.BC_OP_DIVVN,
                        BC_OP.BC_OP_MODVN,
                    ):
                        expr.binary_operation.left_operand = self.new_slot(statement.instruction.b)
                        expr.binary_operation.right_operand = self.new_number(
                            function, statement.instruction.c
                        )
                        statement.assignment.register_slots(expr.binary_operation.left_operand)
                    elif itype in (
                        BC_OP.BC_OP_ADDNV,
                        BC_OP.BC_OP_SUBNV,
                        BC_OP.BC_OP_MULNV,
                        BC_OP.BC_OP_DIVNV,
                        BC_OP.BC_OP_MODNV,
                    ):
                        expr.binary_operation.left_operand = self.new_number(
                            function, statement.instruction.c
                        )
                        expr.binary_operation.right_operand = self.new_slot(statement.instruction.b)
                        statement.assignment.register_slots(expr.binary_operation.right_operand)
                    elif itype in (
                        BC_OP.BC_OP_ADDVV,
                        BC_OP.BC_OP_SUBVV,
                        BC_OP.BC_OP_MULVV,
                        BC_OP.BC_OP_DIVVV,
                        BC_OP.BC_OP_MODVV,
                        BC_OP.BC_OP_POW,
                    ):
                        expr.binary_operation.left_operand = self.new_slot(statement.instruction.b)
                        expr.binary_operation.right_operand = self.new_slot(statement.instruction.c)
                        statement.assignment.register_slots(
                            expr.binary_operation.left_operand,
                            expr.binary_operation.right_operand,
                        )
                    else:
                        expr.binary_operation.left_operand = self.new_slot(statement.instruction.b)
                        current = expr
                        while True:
                            statement.assignment.register_slots(current.binary_operation.left_operand)
                            if (
                                current.binary_operation.left_operand.variable.slot
                                == statement.instruction.c - 1
                            ):
                                current.binary_operation.right_operand = self.new_slot(
                                    statement.instruction.c
                                )
                                statement.assignment.register_slots(current.binary_operation.right_operand)
                                break
                            next_expr = self.new_expression(
                                AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                            )
                            next_expr.binary_operation.type = (
                                AST_BINARY_OPERATION.AST_BINARY_CONCATENATION
                            )
                            next_expr.binary_operation.left_operand = self.new_slot(
                                current.binary_operation.left_operand.variable.slot + 1
                            )
                            current.binary_operation.right_operand = next_expr
                            current = next_expr

                    statement.assignment.expressions[-1] = expr
                    statement.assignment.variables = [
                        AstVariable(type=AST_VARIABLE.AST_VARIABLE_SLOT, slot=statement.instruction.a)
                    ]
                    i -= 1
                    continue

                if itype == BC_OP.BC_OP_KSTR:
                    expr = self.new_string(function, statement.instruction.d)
                    Ast.check_valid_name(expr.constant)
                    statement.assignment.expressions[-1] = expr
                elif itype == BC_OP.BC_OP_KCDATA:
                    statement.assignment.expressions[-1] = self.new_cdata(
                        function, statement.instruction.d
                    )
                elif itype == BC_OP.BC_OP_KSHORT:
                    statement.assignment.expressions[-1] = self.new_signed_literal(
                        statement.instruction.d
                    )
                elif itype == BC_OP.BC_OP_KNUM:
                    statement.assignment.expressions[-1] = self.new_number(
                        function, statement.instruction.d
                    )
                elif itype == BC_OP.BC_OP_KPRI:
                    statement.assignment.expressions[-1] = self.new_primitive(
                        statement.instruction.d
                    )
                elif itype == BC_OP.BC_OP_KNIL:
                    statement.assignment.expressions[-1] = self.new_primitive(0)
                    if statement.instruction.a != statement.instruction.d:
                        new_stmt = self.new_statement(AST_STATEMENT.AST_STATEMENT_INSTRUCTION)
                        new_stmt.instruction = StatementInstruction(
                            type=statement.instruction.type,
                            a=statement.instruction.a,
                            b=statement.instruction.b,
                            c=statement.instruction.c,
                            d=statement.instruction.d - 1,
                            id=statement.instruction.id,
                            target=statement.instruction.target,
                            label=statement.instruction.label,
                        )
                        block.insert(i, new_stmt)
                        i += 1
                        block[i].instruction.a = block[i].instruction.d
                        block[i].instruction.id = INVALID_ID
                        block[i].instruction.label = INVALID_ID
                elif itype == BC_OP.BC_OP_UGET:
                    expr = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_VARIABLE)
                    expr.variable.type = AST_VARIABLE.AST_VARIABLE_UPVALUE
                    expr.variable.slot_scope = function.upvalues[
                        statement.instruction.d
                    ].slot_scope
                    statement.assignment.expressions[-1] = expr
                elif itype in (
                    BC_OP.BC_OP_USETV,
                    BC_OP.BC_OP_USETS,
                    BC_OP.BC_OP_USETN,
                    BC_OP.BC_OP_USETP,
                ):
                    statement.assignment.variables = [
                        AstVariable(type=AST_VARIABLE.AST_VARIABLE_UPVALUE)
                    ]
                    statement.assignment.variables[-1].slot_scope = function.upvalues[
                        statement.instruction.a
                    ].slot_scope
                    if itype == BC_OP.BC_OP_USETV:
                        expr = self.new_slot(statement.instruction.d)
                        statement.assignment.register_slots(expr)
                    elif itype == BC_OP.BC_OP_USETS:
                        expr = self.new_string(function, statement.instruction.d)
                    elif itype == BC_OP.BC_OP_USETN:
                        expr = self.new_number(function, statement.instruction.d)
                    else:
                        expr = self.new_primitive(statement.instruction.d)
                    statement.assignment.expressions[-1] = expr
                    i -= 1
                    continue
                elif itype == BC_OP.BC_OP_FNEW:
                    expr = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_FUNCTION)
                    expr.function = statement.function
                    statement.assignment.expressions[-1] = expr
                elif itype == BC_OP.BC_OP_TNEW:
                    statement.assignment.expressions[-1] = self.new_expression(
                        AST_EXPRESSION.AST_EXPRESSION_TABLE
                    )
                    statement.assignment.is_table_constructor = True
                elif itype == BC_OP.BC_OP_TDUP:
                    statement.assignment.expressions[-1] = self.new_table(
                        function, statement.instruction.d
                    )
                    statement.assignment.is_table_constructor = True
                elif itype == BC_OP.BC_OP_GGET:
                    expr = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_VARIABLE)
                    expr.variable.type = AST_VARIABLE.AST_VARIABLE_GLOBAL
                    expr.variable.name = function.get_constant(statement.instruction.d).string
                    statement.assignment.expressions[-1] = expr
                    if function.has_debug_info:
                        function.used_globals.append(
                            function.get_constant(statement.instruction.d).string
                        )
                elif itype == BC_OP.BC_OP_GSET:
                    var = AstVariable(type=AST_VARIABLE.AST_VARIABLE_GLOBAL)
                    var.name = function.get_constant(statement.instruction.d).string
                    statement.assignment.variables = [var]
                    expr = self.new_slot(statement.instruction.a)
                    statement.assignment.expressions[-1] = expr
                    statement.assignment.register_slots(expr)
                    if function.has_debug_info:
                        function.used_globals.append(
                            function.get_constant(statement.instruction.d).string
                        )
                    i -= 1
                    continue
                elif itype in (BC_OP.BC_OP_TGETV, BC_OP.BC_OP_TGETS, BC_OP.BC_OP_TGETB):
                    expr = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_VARIABLE)
                    expr.variable.type = AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                    expr.variable.table = self.new_slot(statement.instruction.b)
                    statement.assignment.register_slots(expr.variable.table)
                    if itype == BC_OP.BC_OP_TGETV:
                        expr.variable.table_index = self.new_slot(statement.instruction.c)
                        statement.assignment.register_slots(expr.variable.table_index)
                    elif itype == BC_OP.BC_OP_TGETS:
                        expr.variable.table_index = self.new_string(function, statement.instruction.c)
                        Ast.check_valid_name(expr.variable.table_index.constant)
                    else:
                        expr.variable.table_index = self.new_literal(statement.instruction.c)
                    statement.assignment.expressions[-1] = expr
                elif itype in (BC_OP.BC_OP_TSETV, BC_OP.BC_OP_TSETS, BC_OP.BC_OP_TSETB):
                    var = AstVariable(type=AST_VARIABLE.AST_VARIABLE_TABLE_INDEX)
                    var.table = self.new_slot(statement.instruction.b)
                    if itype == BC_OP.BC_OP_TSETV:
                        var.table_index = self.new_slot(statement.instruction.c)
                        statement.assignment.register_slots(var.table_index)
                    elif itype == BC_OP.BC_OP_TSETS:
                        var.table_index = self.new_string(function, statement.instruction.c)
                        Ast.check_valid_name(var.table_index.constant)
                    else:
                        var.table_index = self.new_literal(statement.instruction.c)
                    statement.assignment.variables = [var]
                    expr = self.new_slot(statement.instruction.a)
                    statement.assignment.expressions[-1] = expr
                    statement.assignment.register_slots(expr)
                    i -= 1
                    continue
                elif itype == BC_OP.BC_OP_TSETM:
                    var = AstVariable(type=AST_VARIABLE.AST_VARIABLE_TABLE_INDEX, is_multres=True)
                    var.table = self.new_slot(statement.instruction.a - 1)
                    number_constant = function.get_number_constant(statement.instruction.d)
                    decompiler_assert(
                        number_constant.type == BC_KNUM.BC_KNUM_NUM
                        and (number_constant.number & 0xFFFFFFFF) != 0,
                        "Multres table index is not a valid number constant",
                        self.bytecode.file_path,
                        "Ast::build_expressions",
                        __file__,
                        0,
                    )
                    # The numeric payload is 64 bits; the multires index
                    # uses only its low 32 bits.
                    var.multres_index = int(number_constant.number & 0xFFFFFFFF)
                    expr = self.new_slot(statement.instruction.a)
                    expr.variable.is_multres = True
                    statement.assignment.variables = [var]
                    statement.assignment.expressions[-1] = expr
                    statement.assignment.register_slots(expr)
                    i -= 1
                    continue
                elif itype in (BC_OP.BC_OP_CALLM, BC_OP.BC_OP_CALL):
                    call_expr = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL)
                    if statement.instruction.b:
                        if statement.instruction.b == 1:
                            statement.type = AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL
                        else:
                            statement.assignment.variables = []
                            for j in range(statement.instruction.b - 2, -1, -1):
                                statement.assignment.variables.insert(
                                    0,
                                    AstVariable(
                                        type=AST_VARIABLE.AST_VARIABLE_SLOT,
                                        slot=statement.instruction.a + j,
                                    ),
                                )
                            call_expr.function_call.return_count = len(statement.assignment.variables)
                    else:
                        statement.assignment.variables = [
                            AstVariable(
                                type=AST_VARIABLE.AST_VARIABLE_SLOT,
                                slot=statement.instruction.a,
                                is_multres=True,
                            )
                        ]
                    call_expr.function_call.function = self.new_slot(statement.instruction.a)
                    statement.assignment.register_slots(call_expr.function_call.function)
                    arg_count = statement.instruction.c + (
                        0 if itype == BC_OP.BC_OP_CALLM else -1
                    )
                    call_expr.function_call.arguments = [None] * arg_count  # type: ignore[list-item]
                    if arg_count:
                        statement.assignment.is_potential_method = True
                    for j in range(arg_count):
                        arg = self.new_slot(
                            statement.instruction.a + (2 if self.is_fr2_enabled else 1) + j
                        )
                        call_expr.function_call.arguments[j] = arg
                        statement.assignment.register_slots(arg)
                    if itype == BC_OP.BC_OP_CALLM:
                        m = self.new_slot(
                            statement.instruction.a
                            + (2 if self.is_fr2_enabled else 1)
                            + statement.instruction.c
                        )
                        m.variable.is_multres = True
                        call_expr.function_call.multres_argument = m
                        statement.assignment.register_slots(m)
                    statement.assignment.expressions[-1] = call_expr
                    i -= 1
                    continue
                elif itype == BC_OP.BC_OP_VARG:
                    varg = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_VARARG)
                    if statement.instruction.b:
                        if statement.instruction.b == 1:
                            statement.type = AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL
                        else:
                            statement.assignment.variables = []
                            for j in range(statement.instruction.b - 2, -1, -1):
                                statement.assignment.variables.insert(
                                    0,
                                    AstVariable(
                                        type=AST_VARIABLE.AST_VARIABLE_SLOT,
                                        slot=statement.instruction.a + j,
                                    ),
                                )
                            varg.return_count = len(statement.assignment.variables)
                    else:
                        statement.assignment.variables = [
                            AstVariable(
                                type=AST_VARIABLE.AST_VARIABLE_SLOT,
                                slot=statement.instruction.a,
                                is_multres=True,
                            )
                        ]
                    statement.assignment.expressions[-1] = varg
                    i -= 1
                    continue
                else:
                    decompiler_assert(
                        False,
                        f"Unhandled instruction in build_expressions: {itype}",
                        self.bytecode.file_path,
                        "Ast::build_expressions",
                        __file__,
                        0,
                    )

                if statement.assignment.variables:
                    i -= 1
                    continue
                statement.assignment.variables = [
                    AstVariable(type=AST_VARIABLE.AST_VARIABLE_SLOT, slot=statement.instruction.a)
                ]
                i -= 1
                continue

            if block[i].type == AST_STATEMENT.AST_STATEMENT_RETURN:
                statement = block[i]
                if (
                    i > 0
                    and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_EMPTY
                    and block[i - 1].instruction.type == BC_OP.BC_OP_UCLO
                    and not function.is_valid_label(statement.instruction.label)
                ):
                    statement.instruction.id = block[i - 1].instruction.id
                    statement.instruction.label = block[i - 1].instruction.label
                    i -= 1
                    block.pop(i)
                    statement = block[i]

                itype = statement.instruction.type
                if itype in (BC_OP.BC_OP_CALLMT, BC_OP.BC_OP_CALLT):
                    statement.assignment.multres_return = self.new_expression(
                        AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                    )
                    fcall = statement.assignment.multres_return.function_call
                    fcall.function = self.new_slot(statement.instruction.a)
                    statement.assignment.register_slots(fcall.function)
                    arg_count = statement.instruction.d + (
                        0 if itype == BC_OP.BC_OP_CALLMT else -1
                    )
                    fcall.arguments = [None] * arg_count  # type: ignore[list-item]
                    if arg_count:
                        statement.assignment.is_potential_method = True
                    for j in range(arg_count):
                        arg = self.new_slot(
                            statement.instruction.a + (2 if self.is_fr2_enabled else 1) + j
                        )
                        fcall.arguments[j] = arg
                        statement.assignment.register_slots(arg)
                    if itype == BC_OP.BC_OP_CALLMT:
                        m = self.new_slot(
                            statement.instruction.a
                            + (2 if self.is_fr2_enabled else 1)
                            + statement.instruction.d
                        )
                        m.variable.is_multres = True
                        fcall.multres_argument = m
                        statement.assignment.register_slots(m)
                elif itype in (BC_OP.BC_OP_RETM, BC_OP.BC_OP_RET, BC_OP.BC_OP_RET1):
                    count = (
                        1
                        if itype == BC_OP.BC_OP_RET1
                        else statement.instruction.d + (0 if itype == BC_OP.BC_OP_RETM else -1)
                    )
                    statement.assignment.expressions = [None] * count  # type: ignore[list-item]
                    for j in range(count):
                        expr = self.new_slot(statement.instruction.a + j)
                        statement.assignment.expressions[j] = expr
                        statement.assignment.register_slots(expr)
                    if itype == BC_OP.BC_OP_RETM:
                        m = self.new_slot(statement.instruction.a + statement.instruction.d)
                        m.variable.is_multres = True
                        statement.assignment.multres_return = m
                        statement.assignment.register_slots(m)
                i -= 1
                continue

            if block[i].type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                statement = block[i]
                itype = statement.instruction.type
                if itype in (
                    BC_OP.BC_OP_ISLT,
                    BC_OP.BC_OP_ISGE,
                    BC_OP.BC_OP_ISLE,
                    BC_OP.BC_OP_ISGT,
                    BC_OP.BC_OP_ISEQV,
                    BC_OP.BC_OP_ISNEV,
                    BC_OP.BC_OP_ISEQS,
                    BC_OP.BC_OP_ISNES,
                    BC_OP.BC_OP_ISEQN,
                    BC_OP.BC_OP_ISNEN,
                    BC_OP.BC_OP_ISEQP,
                    BC_OP.BC_OP_ISNEP,
                ):
                    statement.assignment.expressions = [None, None]  # type: ignore[list-item]
                    left = self.new_slot(statement.instruction.a)
                    statement.assignment.expressions[0] = left
                    statement.assignment.register_slots(left)
                    if itype in (
                        BC_OP.BC_OP_ISLT,
                        BC_OP.BC_OP_ISGE,
                        BC_OP.BC_OP_ISLE,
                        BC_OP.BC_OP_ISGT,
                    ):
                        statement.condition.allow_slot_swap = True
                    if itype in (
                        BC_OP.BC_OP_ISLT,
                        BC_OP.BC_OP_ISGE,
                        BC_OP.BC_OP_ISLE,
                        BC_OP.BC_OP_ISGT,
                        BC_OP.BC_OP_ISEQV,
                        BC_OP.BC_OP_ISNEV,
                    ):
                        right = self.new_slot(statement.instruction.d)
                        statement.assignment.register_slots(right)
                    elif itype in (BC_OP.BC_OP_ISEQS, BC_OP.BC_OP_ISNES):
                        right = self.new_string(function, statement.instruction.d)
                    elif itype in (BC_OP.BC_OP_ISEQN, BC_OP.BC_OP_ISNEN):
                        right = self.new_number(function, statement.instruction.d)
                    else:
                        right = self.new_primitive(statement.instruction.d)
                    statement.assignment.expressions[1] = right
                    i -= 1
                    continue

                if itype in (BC_OP.BC_OP_ISTC, BC_OP.BC_OP_ISFC):
                    statement.assignment.variables = [
                        AstVariable(type=AST_VARIABLE.AST_VARIABLE_SLOT, slot=statement.instruction.a)
                    ]
                if itype in (
                    BC_OP.BC_OP_ISTC,
                    BC_OP.BC_OP_ISFC,
                    BC_OP.BC_OP_IST,
                    BC_OP.BC_OP_ISF,
                ):
                    expr = self.new_slot(statement.instruction.d)
                    statement.assignment.expressions = [expr]
                    statement.assignment.register_slots(expr)
                    statement.assignment.allowed_constant_type = CONSTANT_TYPE.INVALID_CONSTANT
                i -= 1
                continue

            if block[i].type == AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR:
                statement = block[i]
                statement.assignment.variables = [
                    AstVariable(type=AST_VARIABLE.AST_VARIABLE_SLOT, slot=statement.instruction.a + 3)
                ]
                decompiler_assert(
                    (not function.has_debug_info)
                    or (
                        statement.locals is not None
                        and statement.assignment.variables[-1].slot == statement.locals.base_slot
                        and len(statement.locals.names) == 1
                    ),
                    "Numeric for loop variable does not match with debug info",
                    self.bytecode.file_path,
                    "Ast::build_expressions",
                    __file__,
                    0,
                )
                e0 = self.new_slot(statement.instruction.a)
                e1 = self.new_slot(statement.instruction.a + 1)
                e2 = self.new_slot(statement.instruction.a + 2)
                statement.assignment.expressions = [e0, e1, e2]
                statement.assignment.register_slots(e0, e1, e2)
                i -= 1
                continue

            if block[i].type == AST_STATEMENT.AST_STATEMENT_GENERIC_FOR:
                statement = block[i]
                statement.assignment.variables = []
                for j in range(statement.instruction.b - 2, -1, -1):
                    statement.assignment.variables.insert(
                        0,
                        AstVariable(
                            type=AST_VARIABLE.AST_VARIABLE_SLOT,
                            slot=statement.instruction.a + j,
                        ),
                    )
                decompiler_assert(
                    (not function.has_debug_info)
                    or (
                        statement.locals is not None
                        and statement.assignment.variables[0].slot == statement.locals.base_slot
                        and len(statement.locals.names) == len(statement.assignment.variables)
                    ),
                    "Generic for loop variables do not match with debug info",
                    self.bytecode.file_path,
                    "Ast::build_expressions",
                    __file__,
                    0,
                )
                e0 = self.new_slot(statement.instruction.a - 3)
                e1 = self.new_slot(statement.instruction.a - 2)
                e2 = self.new_slot(statement.instruction.a - 1)
                statement.assignment.expressions = [e0, e1, e2]
                statement.assignment.register_slots(e0, e1, e2)
                i -= 1
                continue

            if block[i].type == AST_STATEMENT.AST_STATEMENT_DECLARATION:
                statement = block[i]
                decompiler_assert(
                    statement.locals is not None,
                    "Declaration missing local info",
                    self.bytecode.file_path,
                    "Ast::build_expressions",
                    __file__,
                    0,
                )
                statement.assignment.variables = []
                statement.assignment.expressions = []
                for j in range(len(statement.locals.names)):
                    var = AstVariable(
                        type=AST_VARIABLE.AST_VARIABLE_SLOT,
                        slot=statement.locals.base_slot + j,
                    )
                    expr = self.new_slot(var.slot)
                    statement.assignment.variables.append(var)
                    statement.assignment.expressions.append(expr)
                    statement.assignment.register_slots(expr)
                i -= 1
                continue
            i -= 1

    def _walk_expression_slots(self, expression: Optional[Expression], out: list[AstVariable]) -> None:
        if expression is None:
            return
        if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
            if expression.variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                out.append(expression.variable)
            elif expression.variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                self._walk_expression_slots(expression.variable.table, out)
                self._walk_expression_slots(expression.variable.table_index, out)
            return
        if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
            self._walk_expression_slots(expression.function_call.function, out)
            for arg in expression.function_call.arguments:
                self._walk_expression_slots(arg, out)
            self._walk_expression_slots(expression.function_call.multres_argument, out)
            return
        if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
            for field in expression.table.fields:
                self._walk_expression_slots(field.key, out)
                self._walk_expression_slots(field.value, out)
            self._walk_expression_slots(expression.table.multres_field, out)
            return
        if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            self._walk_expression_slots(expression.binary_operation.left_operand, out)
            self._walk_expression_slots(expression.binary_operation.right_operand, out)
            return
        if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            self._walk_expression_slots(expression.unary_operation.operand, out)
            return

    def build_slot_scopes(
        self,
        function: Function,
        block: list[Statement],
        previous_block: Optional[BlockInfo],
    ) -> None:
        def build_nil_assignment(slot: int) -> Statement:
            statement = self.new_statement(AST_STATEMENT.AST_STATEMENT_ASSIGNMENT)
            statement.assignment.expressions = [self.new_primitive(0)]
            statement.assignment.variables = [
                AstVariable(type=AST_VARIABLE.AST_VARIABLE_SLOT, slot=slot)
            ]
            return statement

        def expr_slot(expression: Optional[Expression]) -> int:
            if (
                expression is not None
                and expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                and expression.variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                return expression.variable.slot
            return INVALID_ID

        block_info = BlockInfo(block=block, previous_block=previous_block)
        i = len(block) - 1

        while i >= 0:
            statement = block[i]
            stype = statement.type

            if stype in (
                AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR,
                AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
            ):
                for j in range(len(statement.assignment.variables) - 1, -1, -1):
                    slot = statement.assignment.variables[j].slot
                    decompiler_assert(
                        function.slot_scope_collector.slot_infos[slot].active_slot_scope
                        is None,
                        "Slot scope does not match with for loop variable",
                        self.bytecode.file_path,
                        "Ast::build_slot_scopes",
                        __file__,
                        0,
                    )
                    function.slot_scope_collector.begin_scope(
                        slot, statement.instruction.target - 1
                    )

            if stype in (
                AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR,
                AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
                AST_STATEMENT.AST_STATEMENT_LOOP,
            ):
                function.slot_scope_collector.extend_scopes(statement.instruction.id)
                block_info.index = i
                self.build_slot_scopes(
                    function,
                    statement.block,
                    block_info if stype == AST_STATEMENT.AST_STATEMENT_LOOP else None,
                )
                function.slot_scope_collector.merge_scopes(statement.instruction.target - 1)

            elif stype == AST_STATEMENT.AST_STATEMENT_DECLARATION:
                decompiler_assert(
                    statement.locals is not None and statement.assignment.variables,
                    "Declaration missing local data",
                    self.bytecode.file_path,
                    "Ast::build_slot_scopes",
                    __file__,
                    0,
                )
                statement.instruction.id = INVALID_ID

                j = len(function.slot_scope_collector.slot_infos) - 1
                while j >= statement.locals.base_slot:
                    info_j = function.slot_scope_collector.slot_infos[j]
                    if info_j.active_slot_scope is None:
                        j -= 1
                        continue

                    k = j
                    while True:
                        info_k = function.slot_scope_collector.slot_infos[k]
                        decompiler_assert(
                            info_k.active_slot_scope is not None
                            and info_k.min_scope_begin == INVALID_ID,
                            "Slot scope does not match with variable debug info",
                            self.bytecode.file_path,
                            "Ast::build_slot_scopes",
                            __file__,
                            0,
                        )
                        block.insert(i + 1, build_nil_assignment(k))
                        block[i + 1].assignment.variables[-1].slot_scope = (
                            function.slot_scope_collector.close_scope(
                                k, statement.locals.scope_end
                            )
                        )
                        if k == statement.locals.base_slot:
                            break
                        k -= 1
                    break

                for j in range(len(statement.assignment.variables) - 1, -1, -1):
                    function.slot_scope_collector.begin_scope(
                        statement.assignment.variables[j].slot, statement.locals.scope_end
                    )

                function.slot_scope_collector.extend_scopes(statement.locals.scope_begin)
                block_info.index = i
                self.build_slot_scopes(function, statement.block, block_info)

                j = len(function.slot_scope_collector.slot_infos) - 1
                min_slot = statement.assignment.variables[-1].slot + 1
                while j >= min_slot:
                    info_j = function.slot_scope_collector.slot_infos[j]
                    if info_j.active_slot_scope is None:
                        j -= 1
                        continue

                    k = j
                    while True:
                        info_k = function.slot_scope_collector.slot_infos[k]
                        decompiler_assert(
                            info_k.active_slot_scope is not None
                            and info_k.min_scope_begin == INVALID_ID,
                            "Slot scope does not match with variable debug info",
                            self.bytecode.file_path,
                            "Ast::build_slot_scopes",
                            __file__,
                            0,
                        )
                        statement.block.insert(0, build_nil_assignment(k))
                        statement.block[0].assignment.variables[-1].slot_scope = (
                            function.slot_scope_collector.close_scope(
                                k, statement.locals.scope_begin
                            )
                        )
                        if k == min_slot:
                            break
                        k -= 1
                    break

            if statement.instruction.id != INVALID_ID:
                id_ = statement.instruction.id
                block_info.index = i
                target_label = Ast.get_label_from_next_statement(
                    function, block_info, False, True
                )
                extended_target_label = Ast.get_label_from_next_statement(
                    function, block_info, True, True
                )

                if (
                    function.is_valid_label(target_label)
                    and function.labels[target_label].jump_ids[0] < id_
                    and (
                        extended_target_label == target_label
                        or function.labels[extended_target_label].target > id_
                        or function.labels[extended_target_label].target
                        < function.labels[target_label].jump_ids[0]
                    )
                ):
                    index = Ast.get_block_index_from_id(
                        block, function.labels[target_label].jump_ids[0] - 1
                    )
                    if index != INVALID_ID:
                        is_possible_condition = False
                        has_bool_construct = False
                        target_slot = INVALID_ID
                        condition_blocks: list[list[Statement]] = []

                        if stype == AST_STATEMENT.AST_STATEMENT_CONDITION:
                            if (
                                not statement.assignment.variables
                                and statement.instruction.target
                                == function.labels[extended_target_label].target
                            ):
                                target_stmt = block[index]
                                if target_stmt.type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                                    if len(target_stmt.assignment.expressions) == 1:
                                        if target_stmt.assignment.variables:
                                            var = target_stmt.assignment.variables[-1]
                                            info = function.slot_scope_collector.slot_infos[
                                                var.slot
                                            ]
                                            if (
                                                info.active_slot_scope is not None
                                                and info.min_scope_begin
                                                == target_stmt.instruction.id
                                            ):
                                                is_possible_condition = True
                                                target_slot = var.slot
                                        else:
                                            slot = expr_slot(
                                                target_stmt.assignment.expressions[-1]
                                            )
                                            if slot != INVALID_ID:
                                                info = (
                                                    function.slot_scope_collector.slot_infos[
                                                        slot
                                                    ]
                                                )
                                                if (
                                                    info.active_slot_scope is not None
                                                    and info.min_scope_begin
                                                    == target_stmt.instruction.id
                                                ):
                                                    is_possible_condition = True
                                                    target_slot = slot
                                elif (
                                    target_stmt.type
                                    == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                    and len(target_stmt.assignment.variables) == 1
                                    and target_stmt.assignment.variables[-1].type
                                    == AST_VARIABLE.AST_VARIABLE_SLOT
                                    and function.slot_scope_collector.slot_infos[
                                        target_stmt.assignment.variables[-1].slot
                                    ].active_slot_scope
                                    is not None
                                    and function.slot_scope_collector.slot_infos[
                                        target_stmt.assignment.variables[-1].slot
                                    ].min_scope_begin
                                    == target_stmt.instruction.id
                                    and Ast.get_constant_type(
                                        target_stmt.assignment.expressions[-1]
                                    )
                                    != CONSTANT_TYPE.INVALID_CONSTANT
                                ):
                                    is_possible_condition = True
                                    target_slot = target_stmt.assignment.variables[-1].slot

                        elif stype == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                            if len(statement.assignment.variables) == 1:
                                target_var = statement.assignment.variables[-1]
                                if target_var.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                                    info = function.slot_scope_collector.slot_infos[
                                        target_var.slot
                                    ]
                                    if (
                                        info.active_slot_scope is not None
                                        and info.min_scope_begin == block[index].instruction.id
                                    ):
                                        is_possible_condition = True
                                        target_slot = target_var.slot

                                        if (
                                            i >= 5
                                            and index <= i - 4
                                            and (
                                                (
                                                    block[i - 3].type
                                                    in (
                                                        AST_STATEMENT.AST_STATEMENT_GOTO,
                                                        AST_STATEMENT.AST_STATEMENT_BREAK,
                                                    )
                                                    and not function.is_valid_label(
                                                        block[i - 3].instruction.label
                                                    )
                                                    and block[i - 3].instruction.target
                                                    == function.labels[
                                                        extended_target_label
                                                    ].target
                                                )
                                                or (
                                                    block[i - 3].type
                                                    == AST_STATEMENT.AST_STATEMENT_CONDITION
                                                    and len(
                                                        block[i - 3].assignment.expressions
                                                    )
                                                    == 2
                                                    and block[i - 3].instruction.target
                                                    == statement.instruction.id
                                                )
                                            )
                                            and statement.assignment.expressions[-1].type
                                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                            and statement.assignment.expressions[
                                                -1
                                            ].constant.type
                                            == AST_CONSTANT.AST_CONSTANT_TRUE
                                            and block[i - 1].type
                                            in (
                                                AST_STATEMENT.AST_STATEMENT_GOTO,
                                                AST_STATEMENT.AST_STATEMENT_BREAK,
                                            )
                                            and not function.is_valid_label(
                                                block[i - 1].instruction.label
                                            )
                                            and block[i - 1].instruction.target
                                            == function.labels[target_label].target
                                            and block[i - 2].type
                                            == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                            and block[i - 2].assignment.expressions[-1].type
                                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                            and block[i - 2].assignment.expressions[
                                                -1
                                            ].constant.type
                                            == AST_CONSTANT.AST_CONSTANT_FALSE
                                            and (
                                                function.is_valid_label(
                                                    statement.instruction.label
                                                )
                                                or function.is_valid_label(
                                                    block[i - 2].instruction.label
                                                )
                                            )
                                        ):
                                            has_bool_construct = True

                                elif (
                                    target_var.type
                                    == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                                    and target_var.table is not None
                                    and target_var.table.type
                                    == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                    and target_var.table.variable.type
                                    == AST_VARIABLE.AST_VARIABLE_SLOT
                                ):
                                    table_slot = target_var.table.variable.slot
                                    info = function.slot_scope_collector.slot_infos[table_slot]
                                    if (
                                        info.active_slot_scope is not None
                                        and info.min_scope_begin == block[index].instruction.id
                                    ):
                                        is_possible_condition = True
                                        target_slot = table_slot

                        if is_possible_condition:
                            if has_bool_construct:
                                condition_blocks = [
                                    [block[i]],
                                    [block[i - 2], block[i - 1]],
                                ]
                                index = (
                                    i - 3
                                    if block[i - 3].type
                                    == AST_STATEMENT.AST_STATEMENT_CONDITION
                                    else i - 4
                                )
                            else:
                                index = i

                            if (not has_bool_construct) or index == i - 4:
                                is_possible_condition = False
                                if (
                                    block[index].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                    and len(block[index].assignment.variables) == 1
                                    and block[index].assignment.variables[-1].type
                                    == AST_VARIABLE.AST_VARIABLE_SLOT
                                ):
                                    if (
                                        block[index].assignment.variables[-1].slot
                                        == target_slot
                                    ):
                                        is_possible_condition = True
                                elif (
                                    (
                                        block[index].type
                                        == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                        and len(block[index].assignment.variables) == 1
                                        and block[index].assignment.variables[-1].type
                                        == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                                        and block[index].assignment.variables[
                                            -1
                                        ].table.variable.slot
                                        == target_slot
                                    )
                                    or (
                                        block[index].type
                                        == AST_STATEMENT.AST_STATEMENT_CONDITION
                                        and block[index].instruction.target
                                        == function.labels[extended_target_label].target
                                        and not block[index].assignment.variables
                                    )
                                ):
                                    while index:
                                        index -= 1
                                        scan_stmt = block[index]
                                        if (
                                            scan_stmt.type
                                            == AST_STATEMENT.AST_STATEMENT_CONDITION
                                            and not scan_stmt.assignment.variables
                                            and scan_stmt.instruction.target
                                            == function.labels[extended_target_label].target
                                        ):
                                            continue
                                        if scan_stmt.type in (
                                            AST_STATEMENT.AST_STATEMENT_GOTO,
                                            AST_STATEMENT.AST_STATEMENT_BREAK,
                                        ):
                                            if (
                                                scan_stmt.instruction.target
                                                == function.labels[target_label].target
                                                or scan_stmt.instruction.target
                                                == function.labels[
                                                    extended_target_label
                                                ].target
                                                or scan_stmt.instruction.target
                                                > block[
                                                    i - 4 if has_bool_construct else i
                                                ].instruction.id
                                            ):
                                                break
                                            continue
                                        if (
                                            scan_stmt.type
                                            == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                            and len(scan_stmt.assignment.variables) == 1
                                            and scan_stmt.assignment.variables[-1].type
                                            == AST_VARIABLE.AST_VARIABLE_SLOT
                                            and scan_stmt.assignment.variables[-1].slot
                                            == target_slot
                                        ):
                                            if (
                                                scan_stmt.assignment.is_table_constructor
                                                and (
                                                    has_bool_construct
                                                    or scan_stmt.instruction.id
                                                    > function.labels[target_label].jump_ids[
                                                        0
                                                    ]
                                                )
                                                and function.is_valid_block_range(
                                                    scan_stmt.instruction.id,
                                                    block[
                                                        i - 4
                                                        if has_bool_construct
                                                        else i
                                                    ].instruction.id,
                                                    True,
                                                )
                                            ):
                                                is_possible_condition = True
                                            break

                            block_index = i - 3 if has_bool_construct else i
                            while is_possible_condition:
                                if (
                                    block[index].instruction.id
                                    < function.labels[target_label].jump_ids[0]
                                ):
                                    condition_blocks.append(block[index : block_index + 1])
                                    break

                                is_possible_condition = False
                                while index:
                                    index -= 1
                                    scan_stmt = block[index]
                                    if scan_stmt.type in (
                                        AST_STATEMENT.AST_STATEMENT_CONDITION,
                                        AST_STATEMENT.AST_STATEMENT_GOTO,
                                        AST_STATEMENT.AST_STATEMENT_BREAK,
                                    ):
                                        if (
                                            scan_stmt.instruction.target
                                            != function.labels[target_label].target
                                        ):
                                            continue
                                    else:
                                        continue

                                    condition_blocks.append(block[index + 1 : block_index + 1])
                                    block_index = index

                                    if (
                                        scan_stmt.type
                                        == AST_STATEMENT.AST_STATEMENT_CONDITION
                                    ):
                                        if (
                                            len(scan_stmt.assignment.expressions) == 1
                                            and scan_stmt.assignment.variables
                                        ):
                                            if (
                                                scan_stmt.assignment.variables[-1].slot
                                                == target_slot
                                            ):
                                                is_possible_condition = True
                                        elif (
                                            len(scan_stmt.assignment.expressions) == 1
                                            and index
                                            and expr_slot(
                                                scan_stmt.assignment.expressions[-1]
                                            )
                                            == target_slot
                                        ):
                                            index -= 1
                                            prev_stmt = block[index]
                                            if (
                                                prev_stmt.type
                                                == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                                and len(prev_stmt.assignment.variables)
                                                == 1
                                                and prev_stmt.assignment.variables[
                                                    -1
                                                ].type
                                                == AST_VARIABLE.AST_VARIABLE_SLOT
                                                and prev_stmt.assignment.variables[-1].slot
                                                == target_slot
                                                and not function.is_valid_label(
                                                    block[index + 1].instruction.label
                                                )
                                            ):
                                                is_possible_condition = True
                                            elif (
                                                (
                                                    prev_stmt.type
                                                    == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                                    and len(prev_stmt.assignment.variables)
                                                    == 1
                                                    and prev_stmt.assignment.variables[
                                                        -1
                                                    ].type
                                                    == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                                                    and prev_stmt.assignment.variables[
                                                        -1
                                                    ].table
                                                    is not None
                                                    and prev_stmt.assignment.variables[
                                                        -1
                                                    ].table.type
                                                    == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                                    and prev_stmt.assignment.variables[
                                                        -1
                                                    ].table.variable.type
                                                    == AST_VARIABLE.AST_VARIABLE_SLOT
                                                    and prev_stmt.assignment.variables[
                                                        -1
                                                    ].table.variable.slot
                                                    == target_slot
                                                    and not function.is_valid_label(
                                                        block[index + 1].instruction.label
                                                    )
                                                )
                                                or (
                                                    prev_stmt.type
                                                    == AST_STATEMENT.AST_STATEMENT_CONDITION
                                                    and prev_stmt.instruction.target
                                                    == block[block_index].instruction.id
                                                    and not prev_stmt.assignment.variables
                                                )
                                            ):
                                                while index:
                                                    index -= 1
                                                    prev_scan_stmt = block[index]
                                                    if (
                                                        prev_scan_stmt.type
                                                        == AST_STATEMENT.AST_STATEMENT_CONDITION
                                                        and not prev_scan_stmt.assignment.variables
                                                        and prev_scan_stmt.instruction.target
                                                        == block[block_index].instruction.id
                                                    ):
                                                        continue
                                                    if prev_scan_stmt.type in (
                                                        AST_STATEMENT.AST_STATEMENT_GOTO,
                                                        AST_STATEMENT.AST_STATEMENT_BREAK,
                                                    ):
                                                        if (
                                                            prev_scan_stmt.instruction.target
                                                            == function.labels[
                                                                target_label
                                                            ].target
                                                            or prev_scan_stmt.instruction.target
                                                            == function.labels[
                                                                extended_target_label
                                                            ].target
                                                            or prev_scan_stmt.instruction.target
                                                            >= block[
                                                                block_index
                                                            ].instruction.id
                                                        ):
                                                            break
                                                        continue
                                                    if (
                                                        prev_scan_stmt.type
                                                        == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                                        and len(
                                                            prev_scan_stmt.assignment.variables
                                                        )
                                                        == 1
                                                        and prev_scan_stmt.assignment.variables[
                                                            -1
                                                        ].type
                                                        == AST_VARIABLE.AST_VARIABLE_SLOT
                                                        and prev_scan_stmt.assignment.variables[
                                                            -1
                                                        ].slot
                                                        == target_slot
                                                    ):
                                                        if (
                                                            prev_scan_stmt.assignment.is_table_constructor
                                                            and function.is_valid_block_range(
                                                                prev_scan_stmt.instruction.id,
                                                                block[
                                                                    block_index
                                                                ].instruction.id,
                                                                True,
                                                            )
                                                        ):
                                                            is_possible_condition = True
                                                        break

                                    elif scan_stmt.type in (
                                        AST_STATEMENT.AST_STATEMENT_GOTO,
                                        AST_STATEMENT.AST_STATEMENT_BREAK,
                                    ):
                                        if index:
                                            index -= 1
                                            prev_stmt = block[index]
                                            if (
                                                len(prev_stmt.assignment.variables) == 1
                                                and prev_stmt.assignment.variables[-1].type
                                                == AST_VARIABLE.AST_VARIABLE_SLOT
                                                and prev_stmt.assignment.variables[-1].slot
                                                == target_slot
                                                and Ast.get_constant_type(
                                                    prev_stmt.assignment.expressions[-1]
                                                )
                                                != CONSTANT_TYPE.INVALID_CONSTANT
                                            ):
                                                is_possible_condition = True

                                    break

                            if is_possible_condition:
                                for j in range(index, i + 1):
                                    cur = block[j]
                                    valid = False
                                    if cur.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                                        if (
                                            len(cur.assignment.variables) == 1
                                            and cur.assignment.variables[-1].type
                                            in (
                                                AST_VARIABLE.AST_VARIABLE_SLOT,
                                                AST_VARIABLE.AST_VARIABLE_TABLE_INDEX,
                                            )
                                        ):
                                            valid = True
                                            if (
                                                cur.assignment.variables[-1].type
                                                == AST_VARIABLE.AST_VARIABLE_SLOT
                                                and cur.function is not None
                                                and any(
                                                    upvalue.local and upvalue.slot == target_slot
                                                    for upvalue in cur.function.upvalues
                                                )
                                            ):
                                                valid = False
                                    elif cur.type in (
                                        AST_STATEMENT.AST_STATEMENT_GOTO,
                                        AST_STATEMENT.AST_STATEMENT_BREAK,
                                    ):
                                        if (
                                            not function.is_valid_label(
                                                cur.instruction.label
                                            )
                                            and cur.instruction.type == BC_OP.BC_OP_JMP
                                        ):
                                            target_id = cur.instruction.target
                                            valid = (
                                                target_id
                                                == function.labels[target_label].target
                                                or target_id
                                                == function.labels[
                                                    extended_target_label
                                                ].target
                                                or (
                                                    target_id <= id_
                                                    and target_id > cur.instruction.id
                                                )
                                            )
                                    elif cur.type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                                        target_id = cur.instruction.target
                                        valid = (
                                            target_id
                                            == function.labels[target_label].target
                                            or target_id
                                            == function.labels[extended_target_label].target
                                            or (
                                                target_id <= id_
                                                and target_id > cur.instruction.id
                                            )
                                        )

                                    if valid:
                                        continue
                                    is_possible_condition = False
                                    break

                            if is_possible_condition:
                                for cb_j in range(len(condition_blocks) - 1, -1, -1):
                                    if not is_possible_condition:
                                        break
                                    for cb_k in range(len(condition_blocks[cb_j]) - 1, -1, -1):
                                        cb_stmt = condition_blocks[cb_j][cb_k]
                                        if (
                                            not function.is_valid_label(cb_stmt.instruction.label)
                                            or function.labels[cb_stmt.instruction.label].jump_ids[-1]
                                            < cb_stmt.instruction.id
                                        ):
                                            continue
                                        is_possible_condition = False
                                        break

                            if is_possible_condition and target_slot != INVALID_ID:
                                target_slot_scope = function.slot_scope_collector.slot_infos[
                                    target_slot
                                ].active_slot_scope
                                if target_slot_scope is not None:
                                    target_info = function.slot_scope_collector.slot_infos[
                                        target_slot
                                    ]
                                    target_info.min_scope_begin = INVALID_ID
                                    i += 1

                                    for j in range(len(condition_blocks)):
                                        if j and (
                                            (not has_bool_construct)
                                            or j != 2
                                            or condition_blocks[j][-1].type
                                            != AST_STATEMENT.AST_STATEMENT_CONDITION
                                        ):
                                            target_slot_scope.scope.usages += 1
                                            target_info.active_slot_scope = (
                                                target_slot_scope
                                            )

                                        self.build_slot_scopes(
                                            function, condition_blocks[j], None
                                        )
                                        i -= len(condition_blocks[j])
                                        if (
                                            target_info.active_slot_scope is None
                                            or j == len(condition_blocks) - 1
                                        ):
                                            continue

                                        while (
                                            target_info.slot_scopes
                                            and target_info.slot_scopes[-1]
                                            is not target_slot_scope
                                        ):
                                            merged_cell = target_info.slot_scopes[-1]
                                            target_scope = target_slot_scope.scope
                                            merged_scope = merged_cell.scope
                                            target_scope.usages += (
                                                merged_scope.usages + 1
                                            )
                                            for merged_ref in merged_scope.merged_scopes:
                                                merged_ref.scope = target_scope
                                            target_scope.merged_scopes[0:0] = (
                                                merged_scope.merged_scopes
                                            )
                                            target_scope.merged_scopes.append(
                                                merged_scope.slot_scope
                                            )
                                            merged_cell.scope = target_scope
                                            target_info.slot_scopes.pop()

                                        target_info.active_slot_scope = target_slot_scope
                                        function.slot_scope_collector.extend_scope(
                                            target_slot,
                                            function.get_scope_begin_from_label(
                                                target_label,
                                                target_slot_scope.scope.scope_end,
                                            ),
                                        )
                                        break

                                    i -= 1
                                    continue

            else:
                id_ = function.slot_scope_collector.previous_id - 1

            function.slot_scope_collector.begin_upvalue_scopes(id_)

            if statement.function is not None:
                for j in range(len(statement.function.upvalues) - 1, -1, -1):
                    upvalue = statement.function.upvalues[j]
                    if not upvalue.local:
                        continue
                    if (
                        statement.assignment.variables
                        and upvalue.slot == statement.assignment.variables[-1].slot
                    ):
                        statement.function.assignment_slot_is_upvalue = True
                    upvalue.slot_scope = function.slot_scope_collector.add_to_scope(
                        upvalue.slot, id_
                    )

            for j in range(len(statement.assignment.variables) - 1, -1, -1):
                variable = statement.assignment.variables[j]
                if variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    info = function.slot_scope_collector.slot_infos[variable.slot]
                    if (
                        stype != AST_STATEMENT.AST_STATEMENT_DECLARATION
                        or info.min_scope_begin >= id_
                    ):
                        variable.slot_scope = function.slot_scope_collector.close_scope(
                            variable.slot, id_
                        )
                        continue

                    index = info.min_scope_begin
                    info.min_scope_begin = INVALID_ID
                    variable.slot_scope = function.slot_scope_collector.close_scope(
                        variable.slot, id_
                    )
                    info.min_scope_begin = index
                    continue

                if (
                    variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                    and variable.table is not None
                    and variable.table.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and variable.table.variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
                ):
                    variable.table.variable.slot_scope = (
                        function.slot_scope_collector.add_to_scope(
                            variable.table.variable.slot, id_
                        )
                    )

            if (
                statement.assignment.variables
                and statement.assignment.variables[0].type == AST_VARIABLE.AST_VARIABLE_SLOT
                and statement.assignment.variables[0].is_multres
            ):
                front_var = statement.assignment.variables[0]
                front_scope = front_var.slot_scope
                active_scope = function.slot_scope_collector.slot_infos[
                    front_var.slot
                ].active_slot_scope
                decompiler_assert(
                    front_scope is not None
                    and front_scope.scope.usages == 1
                    and (active_scope is None or active_scope.scope is not front_scope.scope),
                    "Multres assignment has invalid number of usages",
                    self.bytecode.file_path,
                    "Ast::build_slot_scopes",
                    __file__,
                    0,
                )

            for j in range(len(statement.assignment.open_slots) - 1, -1, -1):
                open_slot = statement.assignment.open_slots[j]
                if (
                    open_slot is None
                    or open_slot.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    or open_slot.variable.type != AST_VARIABLE.AST_VARIABLE_SLOT
                ):
                    continue
                open_slot.variable.slot_scope = function.slot_scope_collector.add_to_scope(
                    open_slot.variable.slot, id_
                )

            if statement.instruction.id != INVALID_ID:
                function.slot_scope_collector.previous_id = id_

                if function.is_valid_label(statement.instruction.label):
                    scope_end = function.get_scope_end_from_label(statement.instruction.label)
                    if scope_end > statement.instruction.id:
                        function.slot_scope_collector.merge_scopes(scope_end)
                    function.slot_scope_collector.extend_scopes(
                        function.get_scope_begin_from_label(
                            statement.instruction.label, scope_end
                        )
                    )

            i -= 1

    def eliminate_slots(
        self,
        function: Function,
        block: list[Statement],
        previous_block: Optional[BlockInfo],
    ) -> None:
        def has_self_reference(target_slot: int, expression: Optional[Expression]) -> bool:
            if expression is None:
                return False

            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION:
                if expression.function is None:
                    return False
                for upvalue in expression.function.upvalues:
                    if upvalue.local and upvalue.slot == target_slot:
                        return True
                return False

            if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
                if expression.variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    return expression.variable.slot == target_slot
                if expression.variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    return has_self_reference(
                        target_slot, expression.variable.table
                    ) or has_self_reference(target_slot, expression.variable.table_index)
                return False

            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
                if has_self_reference(target_slot, expression.function_call.function):
                    return True
                for argument in expression.function_call.arguments:
                    if has_self_reference(target_slot, argument):
                        return True
                return has_self_reference(target_slot, expression.function_call.multres_argument)

            if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
                for field in expression.table.fields:
                    if has_self_reference(target_slot, field.key) or has_self_reference(
                        target_slot, field.value
                    ):
                        return True
                return has_self_reference(target_slot, expression.table.multres_field)

            if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
                return has_self_reference(
                    target_slot, expression.binary_operation.left_operand
                ) or has_self_reference(target_slot, expression.binary_operation.right_operand)

            if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
                return has_self_reference(target_slot, expression.unary_operation.operand)

            return False

        def sync_open_slots(statement: Statement) -> None:
            for k in range(len(statement.assignment.open_slots)):
                statement.assignment.open_slots[k] = statement.assignment.expressions[k]

        def get_slot_scope(variable: AstVariable) -> Optional[SlotScope]:
            if variable.type != AST_VARIABLE.AST_VARIABLE_SLOT or variable.slot_scope is None:
                return None
            return variable.slot_scope.scope

        def same_slot_scope(variable_a: AstVariable, variable_b: AstVariable) -> bool:
            scope_a = get_slot_scope(variable_a)
            scope_b = get_slot_scope(variable_b)
            return scope_a is not None and scope_b is not None and scope_a is scope_b

        def get_scope_begin(variable: AstVariable) -> int:
            scope = get_slot_scope(variable)
            if scope is None:
                return INVALID_ID
            return scope.scope_begin

        i = 0
        while i < len(block):
            statement = block[i]

            if (
                statement.type == AST_STATEMENT.AST_STATEMENT_CONDITION
                and statement.condition.allow_slot_swap
                and i > 0
                and not function.is_valid_label(statement.instruction.label)
                and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and len(block[i - 1].assignment.variables) == 1
                and block[i - 1].assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                and block[i - 1].assignment.variables[-1].slot_scope is not None
                and block[i - 1].assignment.variables[-1].slot_scope.scope.usages == 1
                and len(statement.assignment.expressions) >= 2
                and statement.assignment.expressions[0].type
                == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                and statement.assignment.expressions[0].variable.type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and block[i - 1].assignment.variables[-1].slot
                == statement.assignment.expressions[0].variable.slot
            ):
                expression = statement.assignment.expressions[0]
                statement.assignment.expressions[0] = statement.assignment.expressions[1]
                statement.assignment.expressions[1] = expression
                statement.condition.swapped = True
                # Keep open_slots object references aligned with the
                # swapped expression positions.
                if len(statement.assignment.open_slots) == 2:
                    statement.assignment.open_slots[0], statement.assignment.open_slots[1] = (
                        statement.assignment.open_slots[1],
                        statement.assignment.open_slots[0],
                    )

            if statement.type in (
                AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
                AST_STATEMENT.AST_STATEMENT_DECLARATION,
            ):
                while i > 0 and not function.is_valid_label(statement.instruction.label):
                    prev = block[i - 1]
                    merged_expression_list = False

                    if prev.type in (
                        AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                        AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL,
                    ):
                        if (
                            statement.type == AST_STATEMENT.AST_STATEMENT_GENERIC_FOR
                            and prev.type == AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL
                        ):
                            break
                        if prev.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                            if (
                                statement.assignment.open_slots
                                and len(statement.assignment.expressions)
                                >= len(statement.assignment.open_slots)
                                and statement.assignment.expressions[
                                    len(statement.assignment.open_slots) - 1
                                ].type
                                == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                and statement.assignment.expressions[
                                    len(statement.assignment.open_slots) - 1
                                ].variable.type
                                == AST_VARIABLE.AST_VARIABLE_SLOT
                                and prev.assignment.variables
                                and prev.assignment.variables[0].slot
                                <= statement.assignment.expressions[
                                    len(statement.assignment.open_slots) - 1
                                ].variable.slot
                            ):
                                pass
                            else:
                                if not (
                                    len(prev.assignment.variables) == 1
                                    and prev.assignment.variables[-1].slot_scope is not None
                                    and prev.assignment.variables[-1].slot_scope.scope.usages
                                    == 0
                                ):
                                    break
                                if statement.type == AST_STATEMENT.AST_STATEMENT_GENERIC_FOR:
                                    break
                                statement.assignment.expressions.insert(
                                    len(statement.assignment.open_slots),
                                    prev.assignment.expressions[-1],
                                )
                                statement.instruction.label = prev.instruction.label
                                i -= 1
                                del block[i]
                                statement = block[i]
                                sync_open_slots(statement)
                                merged_expression_list = True
                        else:
                            statement.assignment.expressions.insert(
                                len(statement.assignment.open_slots),
                                prev.assignment.expressions[-1],
                            )
                            statement.instruction.label = prev.instruction.label
                            i -= 1
                            del block[i]
                            statement = block[i]
                            sync_open_slots(statement)
                            merged_expression_list = True

                    if merged_expression_list:
                        continue

                    if (
                        prev.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                        and len(prev.assignment.variables) != 1
                    ):
                        if not (
                            len(statement.assignment.expressions)
                            == len(statement.assignment.open_slots)
                            and statement.assignment.expressions
                            and statement.assignment.expressions[-1].type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and statement.assignment.expressions[-1].variable.type
                            == AST_VARIABLE.AST_VARIABLE_SLOT
                            and statement.assignment.expressions[-1].variable.slot
                            == prev.assignment.variables[-1].slot
                        ):
                            break

                        while True:
                            tail_expression = statement.assignment.expressions[-1]
                            if tail_expression.variable.slot_scope is not None:
                                function.slot_scope_collector.remove_scope(
                                    tail_expression.variable.slot,
                                    tail_expression.variable.slot_scope,
                                )
                            statement.assignment.open_slots.pop()

                            if tail_expression.variable.slot != prev.assignment.variables[0].slot:
                                statement.assignment.expressions.pop()
                                continue

                            statement.assignment.expressions[-1] = prev.assignment.expressions[-1]
                            statement.instruction.label = prev.instruction.label
                            i -= 1
                            del block[i]
                            statement = block[i]
                            break

                        sync_open_slots(statement)
                        continue

                    sync_open_slots(statement)
                    break

            if (
                statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and len(statement.assignment.variables) == 1
            ):
                last_variable = statement.assignment.variables[-1]

                if (
                    last_variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
                    and statement.assignment.expressions
                    and statement.assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                    and statement.assignment.expressions[-1].binary_operation.type
                    != AST_BINARY_OPERATION.AST_BINARY_CONCATENATION
                    and len(statement.assignment.open_slots) == 2
                    and i >= 2
                    and not function.is_valid_label(statement.instruction.label)
                    and not function.is_valid_label(block[i - 1].instruction.label)
                    and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(block[i - 1].assignment.variables) == 1
                    and block[i - 1].assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i - 1].assignment.variables[-1].slot_scope is not None
                    and block[i - 1].assignment.variables[-1].slot_scope.scope.usages == 1
                    and statement.assignment.expressions[-1].binary_operation.left_operand.type
                    == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and statement.assignment.expressions[-1].binary_operation.left_operand.variable.type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i - 1].assignment.variables[-1].slot
                    == statement.assignment.expressions[-1].binary_operation.left_operand.variable.slot
                    and Ast.get_constant_type(block[i - 1].assignment.expressions[-1])
                    == CONSTANT_TYPE.NUMBER_CONSTANT
                    and block[i - 2].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(block[i - 2].assignment.variables) == 1
                    and block[i - 2].assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i - 2].assignment.variables[-1].slot_scope is not None
                    and block[i - 2].assignment.variables[-1].slot_scope.scope.usages == 1
                    and statement.assignment.expressions[-1].binary_operation.right_operand.type
                    == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and statement.assignment.expressions[-1].binary_operation.right_operand.variable.type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i - 2].assignment.variables[-1].slot
                    == statement.assignment.expressions[-1].binary_operation.right_operand.variable.slot
                ):
                    statement.assignment.open_slots[0] = (
                        statement.assignment.expressions[-1].binary_operation.right_operand
                    )
                    statement.assignment.open_slots[1] = (
                        statement.assignment.expressions[-1].binary_operation.left_operand
                    )

                if (
                    last_variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                    and not last_variable.is_multres
                    and i >= 3
                    and not function.is_valid_label(statement.instruction.label)
                    and not function.is_valid_label(block[i - 1].instruction.label)
                    and not function.is_valid_label(block[i - 2].instruction.label)
                    and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(block[i - 1].assignment.variables) == 1
                    and block[i - 1].assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i - 1].assignment.variables[-1].slot_scope is not None
                    and block[i - 1].assignment.variables[-1].slot_scope.scope.usages == 1
                    and last_variable.table_index is not None
                    and last_variable.table_index.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and last_variable.table_index.variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i - 1].assignment.variables[-1].slot
                    == last_variable.table_index.variable.slot
                    and Ast.get_constant_type(block[i - 1].assignment.expressions[-1])
                    != CONSTANT_TYPE.INVALID_CONSTANT
                    and block[i - 2].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(block[i - 2].assignment.variables) == 1
                    and block[i - 2].assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i - 2].assignment.variables[-1].slot_scope is not None
                    and block[i - 2].assignment.variables[-1].slot_scope.scope.usages == 1
                    and statement.assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and statement.assignment.expressions[-1].variable.type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i - 2].assignment.variables[-1].slot
                    == statement.assignment.expressions[-1].variable.slot
                    and (
                        Ast.get_constant_type(block[i - 2].assignment.expressions[-1])
                        == CONSTANT_TYPE.INVALID_CONSTANT
                        or Ast.get_constant_type(block[i - 1].assignment.expressions[-1])
                        == CONSTANT_TYPE.NIL_CONSTANT
                    )
                    and block[i - 3].assignment.is_table_constructor
                    and block[i - 3].assignment.variables
                    and block[i - 3].assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and last_variable.table is not None
                    and last_variable.table.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and last_variable.table.variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i - 3].assignment.variables[-1].slot
                    == last_variable.table.variable.slot
                    and block[i - 3].assignment.expressions
                    and block[i - 3].assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_TABLE
                    and block[i - 3].assignment.expressions[-1].table.multres_field is None
                ):
                    statement.assignment.open_slots[0] = statement.assignment.expressions[-1]
                    statement.assignment.open_slots[1] = last_variable.table_index

            if statement.type in (
                AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR,
                AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
            ):
                self.eliminate_slots(function, statement.block, None)
            elif statement.type in (
                AST_STATEMENT.AST_STATEMENT_LOOP,
                AST_STATEMENT.AST_STATEMENT_DECLARATION,
                AST_STATEMENT.AST_STATEMENT_IF,
                AST_STATEMENT.AST_STATEMENT_ELSE,
                AST_STATEMENT.AST_STATEMENT_WHILE,
                AST_STATEMENT.AST_STATEMENT_REPEAT,
                AST_STATEMENT.AST_STATEMENT_DO,
            ):
                child_prev = BlockInfo(block=block, previous_block=previous_block, index=i)
                self.eliminate_slots(function, statement.block, child_prev)

            if statement.type in (
                AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                AST_STATEMENT.AST_STATEMENT_DECLARATION,
                AST_STATEMENT.AST_STATEMENT_CONDITION,
                AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL,
                AST_STATEMENT.AST_STATEMENT_RETURN,
                AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR,
                AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
            ):
                # Handle declarations captured by an upvalue.
                _did_upvalue_special = False
                if (
                    statement.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and len(statement.assignment.open_slots) == 1
                    and statement.assignment.open_slots[-1] is not None
                    and statement.assignment.open_slots[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and statement.assignment.open_slots[-1].variable.slot_scope is not None
                    and statement.assignment.open_slots[-1].variable.slot_scope.scope.usages > 1
                    and i > 0
                    and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(block[i - 1].assignment.variables) == 1
                    and block[i - 1].assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i - 1].function is not None
                    and block[i - 1].function.assignment_slot_is_upvalue
                    and block[i - 1].assignment.variables[-1].slot
                    == statement.assignment.open_slots[-1].variable.slot
                ):
                    statement.assignment.open_slots[-1].assign_from(
                        block[i - 1].assignment.expressions[-1]
                    )
                    block[i - 1].assignment.variables[-1].slot_scope.scope = (
                        statement.assignment.variables[-1].slot_scope.scope
                    )
                    statement.instruction.label = block[i - 1].instruction.label
                    i -= 1
                    function.slot_scope_collector.remove_scope(
                        block[i].assignment.variables[-1].slot,
                        block[i].assignment.variables[-1].slot_scope,
                    )
                    del block[i]
                    statement = block[i]
                    _did_upvalue_special = True

                j = -1
                if not _did_upvalue_special:
                    j = len(statement.assignment.open_slots) - 1
                while j >= 0 and i > 0:
                    open_slot = statement.assignment.open_slots[j]
                    if (
                        open_slot is None
                        or open_slot.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                        or open_slot.variable.type != AST_VARIABLE.AST_VARIABLE_SLOT
                    ):
                        j -= 1
                        continue
                    if function.is_valid_label(statement.instruction.label):
                        break

                    if (
                        j == 1
                        and statement.assignment.is_potential_method
                        and i >= 2
                        and not function.is_valid_label(block[i - 1].instruction.label)
                        and statement.assignment.open_slots
                        and statement.assignment.open_slots[0] is not None
                        and statement.assignment.open_slots[0].type
                        == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                        and statement.assignment.open_slots[0].variable.type
                        == AST_VARIABLE.AST_VARIABLE_SLOT
                        and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                        and len(block[i - 1].assignment.variables) == 1
                        and block[i - 1].assignment.variables[-1].type
                        == AST_VARIABLE.AST_VARIABLE_SLOT
                        and block[i - 1].assignment.variables[-1].slot
                        == statement.assignment.open_slots[0].variable.slot
                        and block[i - 1].assignment.expressions
                        and block[i - 1].assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                        and block[i - 1].assignment.expressions[-1].variable.type
                        == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                        and block[i - 1].assignment.expressions[-1].variable.table is not None
                        and block[i - 1].assignment.expressions[-1].variable.table.type
                        == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                        and block[i - 1].assignment.expressions[-1].variable.table.variable.type
                        == AST_VARIABLE.AST_VARIABLE_SLOT
                        and block[i - 1].assignment.expressions[-1].variable.table_index
                        is not None
                        and block[i - 1].assignment.expressions[-1].variable.table_index.type
                        == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                        and block[i - 1]
                        .assignment.expressions[-1]
                        .variable.table_index.constant.is_name
                        and block[i - 2].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                        and len(block[i - 2].assignment.variables) == 1
                        and block[i - 2].assignment.variables[-1].type
                        == AST_VARIABLE.AST_VARIABLE_SLOT
                        and block[i - 2].assignment.variables[-1].slot_scope is not None
                        and block[i - 2].assignment.variables[-1].slot_scope.scope.usages == 1
                        and block[i - 2].assignment.variables[-1].slot
                        == open_slot.variable.slot
                        and block[i - 2].assignment.expressions
                        and block[i - 2].assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                        and block[i - 2].assignment.expressions[-1].variable.type
                        == AST_VARIABLE.AST_VARIABLE_SLOT
                        and block[i - 2].assignment.expressions[-1].variable.slot
                        == block[i - 1]
                        .assignment.expressions[-1]
                        .variable.table.variable.slot
                    ):
                        if (
                            statement.type == AST_STATEMENT.AST_STATEMENT_RETURN
                            and statement.assignment.multres_return is not None
                            and statement.assignment.multres_return.type
                            == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                        ):
                            statement.assignment.multres_return.function_call.is_method = True
                            if statement.assignment.multres_return.function_call.arguments:
                                del statement.assignment.multres_return.function_call.arguments[
                                    0
                                ]
                        elif (
                            statement.assignment.expressions
                            and statement.assignment.expressions[-1].type
                            == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                        ):
                            statement.assignment.expressions[-1].function_call.is_method = True
                            if statement.assignment.expressions[-1].function_call.arguments:
                                del statement.assignment.expressions[-1].function_call.arguments[
                                    0
                                ]

                        del statement.assignment.open_slots[j]
                        statement.assignment.open_slots.insert(
                            0,
                            block[i - 1].assignment.expressions[-1].variable.table,
                        )
                        function.slot_scope_collector.remove_scope(
                            block[i - 2].assignment.variables[-1].slot,
                            block[i - 2].assignment.variables[-1].slot_scope,
                        )
                        block[i - 1].instruction.label = block[i - 2].instruction.label
                        if (
                            block[i - 2].assignment.expressions[-1].variable.slot_scope
                            is not None
                        ):
                            block[
                                i - 2
                            ].assignment.expressions[-1].variable.slot_scope.scope.usages -= 1
                        i -= 1
                        del block[i - 1]
                        statement = block[i]
                        if j >= len(statement.assignment.open_slots):
                            j = len(statement.assignment.open_slots) - 1
                        if j < 0:
                            break
                        open_slot = statement.assignment.open_slots[j]
                        if (
                            open_slot is None
                            or open_slot.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            or open_slot.variable.type != AST_VARIABLE.AST_VARIABLE_SLOT
                        ):
                            j -= 1
                            continue

                    prev = block[i - 1]
                    if (
                        prev.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                        and len(prev.assignment.variables) == 1
                        and prev.assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                        and prev.assignment.variables[-1].slot == open_slot.variable.slot
                    ):
                        if prev.assignment.variables[-1].slot_scope is not None:
                            if prev.assignment.variables[-1].slot_scope.scope.usages != 1:
                                break
                        # Save old expression state for potential revert
                        saved_expression = Expression(open_slot.type)
                        saved_expression.assign_from(open_slot)
                        open_slot.assign_from(prev.assignment.expressions[-1])

                        # Check the allowed constant type.
                        # Must check BEFORE remove_scope so revert is clean
                        if (
                            j == 0
                            and statement.assignment.allowed_constant_type
                            != CONSTANT_TYPE.NUMBER_CONSTANT
                            and Ast.get_constant_type(
                                statement.assignment.expressions[-1]
                            )
                            > statement.assignment.allowed_constant_type
                        ):
                            open_slot.assign_from(saved_expression)
                            break

                        # Remove the scope only after the constant-type check passes.
                        if prev.assignment.variables[-1].slot_scope is not None:
                            function.slot_scope_collector.remove_scope(
                                prev.assignment.variables[-1].slot,
                                prev.assignment.variables[-1].slot_scope,
                            )

                        statement.instruction.label = prev.instruction.label
                        del block[i - 1]
                        i -= 1
                        continue
                    j -= 1

            if (
                statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and len(statement.assignment.variables) == 1
                and statement.assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                and statement.instruction.id != INVALID_ID
            ):
                slot_variable = statement.assignment.variables[-1]
                slot_scope = get_slot_scope(slot_variable)
                debug_slot_case = (
                    _verbose_enabled
                    and function.level == 1
                    and function.id == 42
                    and statement.instruction.id in (6, 8)
                )
                if (
                    _verbose_enabled
                    and function.level == 1
                    and function.id == 42
                    and slot_scope is not None
                ):
                    verbose_log(
                        "Debug function[42] slot branch: "
                        f"index={i}, id={statement.instruction.id}, slot={slot_variable.slot}, usages={slot_scope.usages}"
                    )
                block_info = BlockInfo(block=block, previous_block=previous_block, index=i)
                target_label = Ast.get_label_from_next_statement(
                    function, block_info, False, True
                )
                extended_target_label = Ast.get_label_from_next_statement(
                    function, block_info, True, True
                )
                if debug_slot_case:
                    verbose_log(
                        "Debug function[42] slot labels: "
                        f"id={statement.instruction.id}, target_label={target_label}, extended_target_label={extended_target_label}"
                    )

                if (
                    function.is_valid_label(target_label)
                    and function.labels[target_label].jump_ids[0]
                    <= statement.instruction.id
                    and slot_scope is not None
                    and slot_scope.usages >= 2
                ):
                    jump_front = function.labels[target_label].jump_ids[0]
                    if debug_slot_case:
                        verbose_log(
                            "Debug function[42] slot guard pass: "
                            f"id={statement.instruction.id}, jump_front={jump_front}"
                        )
                    if (
                        get_scope_begin(slot_variable) >= jump_front
                        or (
                            extended_target_label != target_label
                            and (
                                function.labels[extended_target_label].target
                                <= statement.instruction.id
                                or function.labels[extended_target_label].target >= jump_front
                            )
                        )
                        or has_self_reference(
                            slot_variable.slot, statement.assignment.expressions[-1]
                        )
                    ):
                        if debug_slot_case:
                            verbose_log(
                                "Debug function[42] slot rejected by preconditions: "
                                f"id={statement.instruction.id}, scope_begin={get_scope_begin(slot_variable)}"
                            )
                        pass
                    else:
                        index = Ast.get_block_index_from_id(block, jump_front - 1)
                        if debug_slot_case:
                            verbose_log(
                                "Debug function[42] slot initial index: "
                                f"id={statement.instruction.id}, index={index}"
                            )
                        if index != INVALID_ID:
                            scan_statement = block[index]
                            if (
                                scan_statement.type
                                == AST_STATEMENT.AST_STATEMENT_CONDITION
                            ):
                                if scan_statement.assignment.variables:
                                    scan_var = scan_statement.assignment.variables[-1]
                                    if not (
                                        get_scope_begin(scan_var)
                                        == scan_statement.instruction.id
                                        and same_slot_scope(scan_var, slot_variable)
                                    ):
                                        index = INVALID_ID
                                else:
                                    if (
                                        not (
                                            index > 0
                                            and len(scan_statement.assignment.expressions) == 1
                                            and not function.is_valid_label(
                                                scan_statement.instruction.label
                                            )
                                            and block[index - 1].type
                                            == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                            and len(block[index - 1].assignment.variables) == 1
                                            and block[index - 1].assignment.variables[-1].type
                                            == AST_VARIABLE.AST_VARIABLE_SLOT
                                            and get_scope_begin(
                                                block[index - 1].assignment.variables[-1]
                                            )
                                            == block[index - 1].instruction.id
                                            and same_slot_scope(
                                                block[index - 1].assignment.variables[-1],
                                                slot_variable,
                                            )
                                        )
                                    ):
                                        index = INVALID_ID
                            elif (
                                scan_statement.type
                                == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                            ):
                                if not (
                                    len(scan_statement.assignment.variables) == 1
                                    and scan_statement.assignment.variables[-1].type
                                    == AST_VARIABLE.AST_VARIABLE_SLOT
                                    and get_scope_begin(
                                        scan_statement.assignment.variables[-1]
                                    )
                                    == scan_statement.instruction.id
                                    and same_slot_scope(
                                        scan_statement.assignment.variables[-1],
                                        slot_variable,
                                    )
                                    and (
                                        index == i - 4
                                        or (
                                            scan_statement.assignment.expressions[-1].type
                                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                            and Ast.get_constant_type(
                                                scan_statement.assignment.expressions[-1]
                                            )
                                            != CONSTANT_TYPE.INVALID_CONSTANT
                                        )
                                    )
                                ):
                                    index = INVALID_ID
                            else:
                                index = INVALID_ID

                        has_bool_construct = False
                        cancel_slot_condition = False
                        if index != INVALID_ID and i >= 3:
                            if (
                                statement.assignment.expressions[-1].type
                                == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                and statement.assignment.expressions[-1].constant.type
                                == AST_CONSTANT.AST_CONSTANT_TRUE
                                and block[i - 1].type
                                in (
                                    AST_STATEMENT.AST_STATEMENT_GOTO,
                                    AST_STATEMENT.AST_STATEMENT_BREAK,
                                )
                                and not function.is_valid_label(
                                    block[i - 1].instruction.label
                                )
                                and block[i - 1].instruction.type == BC_OP.BC_OP_JMP
                                and block[i - 1].instruction.target
                                == function.labels[target_label].target
                                and block[i - 2].type
                                == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                and block[i - 2].assignment.expressions[-1].type
                                == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                and block[i - 2].assignment.expressions[-1].constant.type
                                == AST_CONSTANT.AST_CONSTANT_FALSE
                                and len(block[i - 2].assignment.variables) == 1
                                and block[i - 2].assignment.variables[-1].type
                                == AST_VARIABLE.AST_VARIABLE_SLOT
                                and same_slot_scope(
                                    block[i - 2].assignment.variables[-1],
                                    slot_variable,
                                )
                            ):
                                if (
                                    block[i - 3].type
                                    == AST_STATEMENT.AST_STATEMENT_CONDITION
                                ):
                                    if (
                                        len(block[i - 3].assignment.expressions) == 2
                                        and block[i - 3].instruction.target
                                        == statement.instruction.id
                                    ):
                                        has_bool_construct = True
                                elif block[i - 3].type in (
                                    AST_STATEMENT.AST_STATEMENT_GOTO,
                                    AST_STATEMENT.AST_STATEMENT_BREAK,
                                ):
                                    if (
                                        i < 5
                                        or function.is_valid_label(
                                            block[i - 3].instruction.label
                                        )
                                        or block[i - 3].instruction.type
                                        != BC_OP.BC_OP_JMP
                                        or block[i - 3].instruction.target
                                        != function.labels[extended_target_label].target
                                        or (
                                            not function.is_valid_label(
                                                statement.instruction.label
                                            )
                                            and not function.is_valid_label(
                                                block[i - 2].instruction.label
                                            )
                                        )
                                        or block[i - 4].type
                                        != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                        or len(block[i - 4].assignment.variables) != 1
                                        or block[i - 4].assignment.variables[-1].type
                                        != AST_VARIABLE.AST_VARIABLE_SLOT
                                        or block[i - 4].assignment.variables[-1].slot
                                        != slot_variable.slot
                                    ):
                                        pass
                                    else:
                                        if (
                                            index == i - 2
                                            and not function.is_valid_label(
                                                statement.instruction.label
                                            )
                                        ):
                                            if not function.is_valid_label(
                                                block[i - 2].instruction.label
                                            ) or (
                                                function.labels[
                                                    block[i - 2].instruction.label
                                                ].jump_ids[0]
                                                > block[i - 2].instruction.id
                                            ):
                                                cancel_slot_condition = True
                                            else:
                                                index = Ast.get_block_index_from_id(
                                                    block,
                                                    function.labels[
                                                        block[i - 2].instruction.label
                                                    ].jump_ids[0]
                                                    - 1,
                                                )
                                                if index == INVALID_ID:
                                                    index = i - 2

                                        has_bool_construct = not cancel_slot_condition
                        if debug_slot_case:
                            verbose_log(
                                "Debug function[42] bool state: "
                                f"id={statement.instruction.id}, index={index}, has_bool={has_bool_construct}, cancel={cancel_slot_condition}"
                            )

                        if has_bool_construct and index != INVALID_ID and not cancel_slot_condition:
                            if (
                                (
                                    function.is_valid_label(statement.instruction.label)
                                    and function.labels[
                                        statement.instruction.label
                                    ].jump_ids[-1]
                                    >= statement.instruction.id
                                )
                                or (
                                    function.is_valid_label(block[i - 2].instruction.label)
                                    and function.labels[
                                        block[i - 2].instruction.label
                                    ].jump_ids[-1]
                                    >= block[i - 2].instruction.id
                                )
                            ):
                                cancel_slot_condition = True

                        if has_bool_construct and index != INVALID_ID and not cancel_slot_condition:
                            if function.is_valid_label(statement.instruction.label):
                                for jump_id in reversed(
                                    function.labels[statement.instruction.label].jump_ids
                                ):
                                    target_index = Ast.get_block_index_from_id(
                                        block, jump_id - 1
                                    )
                                    if (
                                        target_index == INVALID_ID
                                        or block[target_index].type
                                        != AST_STATEMENT.AST_STATEMENT_CONDITION
                                        or bool(block[target_index].assignment.variables)
                                    ):
                                        index = INVALID_ID
                                        break
                                    if not block[target_index].assignment.expressions:
                                        has_bool_construct = False
                                        break

                        if has_bool_construct and index != INVALID_ID and not cancel_slot_condition:
                            if function.is_valid_label(block[i - 2].instruction.label):
                                for jump_id in reversed(
                                    function.labels[block[i - 2].instruction.label].jump_ids
                                ):
                                    target_index = Ast.get_block_index_from_id(
                                        block, jump_id - 1
                                    )
                                    if (
                                        target_index == INVALID_ID
                                        or block[target_index].type
                                        != AST_STATEMENT.AST_STATEMENT_CONDITION
                                    ):
                                        index = INVALID_ID
                                        break
                                    if (
                                        not block[target_index].assignment.expressions
                                        or bool(block[target_index].assignment.variables)
                                    ):
                                        has_bool_construct = False
                                        break

                        if cancel_slot_condition:
                            index = INVALID_ID

                        if index != INVALID_ID:
                            j = i
                            while (
                                index != INVALID_ID
                                and block[index].instruction.id < block[j].instruction.id
                            ):
                                if function.is_valid_label(block[j].instruction.label):
                                    if (
                                        function.labels[block[j].instruction.label].jump_ids[-1]
                                        >= block[j].instruction.id
                                    ):
                                        index = INVALID_ID
                                        break
                                    while (
                                        function.labels[block[j].instruction.label].jump_ids[0]
                                        < block[index].instruction.id
                                    ):
                                        if index == 0:
                                            index = INVALID_ID
                                            break
                                        index -= 1
                                j -= 1
                        if debug_slot_case:
                            verbose_log(
                                "Debug function[42] post backtrack index: "
                                f"id={statement.instruction.id}, index={index}"
                            )

                        if index != INVALID_ID:
                            if (
                                block[index].type
                                == AST_STATEMENT.AST_STATEMENT_CONDITION
                            ):
                                if block[index].assignment.variables:
                                    pass
                                elif (
                                    block[index].instruction.target
                                    == function.labels[target_label].target
                                    and index > 0
                                ):
                                    index -= 1
                            elif block[index].type in (
                                AST_STATEMENT.AST_STATEMENT_GOTO,
                                AST_STATEMENT.AST_STATEMENT_BREAK,
                            ):
                                if (
                                    block[index].instruction.target
                                    == function.labels[target_label].target
                                    and index > 0
                                ):
                                    index -= 1

                        if index != INVALID_ID:
                            condition_builder = ConditionBuilder(
                                ConditionBuilderType.ASSIGNMENT,
                                self,
                                target_label,
                                statement.instruction.label if has_bool_construct else INVALID_ID,
                                block[i - 2].instruction.label
                                if has_bool_construct
                                else INVALID_ID,
                            )
                            target_index = (
                                i - 4
                                if (
                                    has_bool_construct
                                    and block[i - 3].type
                                    in (
                                        AST_STATEMENT.AST_STATEMENT_GOTO,
                                        AST_STATEMENT.AST_STATEMENT_BREAK,
                                    )
                                )
                                else (i - 2 if has_bool_construct else i)
                            )
                            valid = True
                            j = index
                            while j < target_index:
                                cur = block[j]
                                if (
                                    cur.type
                                    == AST_STATEMENT.AST_STATEMENT_CONDITION
                                ):
                                    invalid_condition = (
                                        cur.instruction.target <= cur.instruction.id
                                        or cur.instruction.target
                                        > function.labels[target_label].target
                                        or (
                                            (
                                                cur.instruction.target
                                                == function.labels[target_label].target
                                            )
                                            and (
                                                not cur.assignment.variables
                                                or not same_slot_scope(
                                                    cur.assignment.variables[-1],
                                                    slot_variable,
                                                )
                                                or has_self_reference(
                                                    slot_variable.slot,
                                                    cur.assignment.expressions[-1],
                                                )
                                            )
                                        )
                                        or (
                                            cur.instruction.target
                                            != function.labels[target_label].target
                                            and bool(cur.assignment.variables)
                                        )
                                    )
                                    if invalid_condition:
                                        valid = False
                                        break
                                    condition_builder.add_node(
                                        condition_builder.get_node_type(
                                            cur.instruction.type,
                                            cur.condition.swapped,
                                        ),
                                        cur.instruction.label,
                                        function.get_label_from_id(
                                            cur.instruction.target
                                        ),
                                        cur.assignment.expressions,
                                    )
                                    j += 1
                                    continue

                                if (
                                    cur.type
                                    == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                ):
                                    if (
                                        len(cur.assignment.variables) != 1
                                        or cur.assignment.variables[-1].type
                                        != AST_VARIABLE.AST_VARIABLE_SLOT
                                        or not same_slot_scope(
                                            cur.assignment.variables[-1],
                                            slot_variable,
                                        )
                                        or has_self_reference(
                                            slot_variable.slot,
                                            cur.assignment.expressions[-1],
                                        )
                                        or j + 1 == target_index
                                        or function.is_valid_label(
                                            block[j + 1].instruction.label
                                        )
                                    ):
                                        valid = False
                                        break

                                    j += 1
                                    next_statement = block[j]
                                    if (
                                        next_statement.type
                                        == AST_STATEMENT.AST_STATEMENT_CONDITION
                                    ):
                                        if not (
                                            next_statement.instruction.target
                                            == function.labels[target_label].target
                                            and not next_statement.assignment.variables
                                            and len(next_statement.assignment.expressions)
                                            == 1
                                            and next_statement.assignment.expressions[-1].type
                                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                            and next_statement.assignment.expressions[
                                                -1
                                            ].variable.type
                                            == AST_VARIABLE.AST_VARIABLE_SLOT
                                            and same_slot_scope(
                                                next_statement.assignment.expressions[
                                                    -1
                                                ].variable,
                                                slot_variable,
                                            )
                                        ):
                                            valid = False
                                            break
                                        condition_builder.add_node(
                                            condition_builder.get_node_type(
                                                next_statement.instruction.type,
                                                next_statement.condition.swapped,
                                            ),
                                            cur.instruction.label,
                                            function.get_label_from_id(
                                                next_statement.instruction.target
                                            ),
                                            cur.assignment.expressions,
                                        )
                                        j += 1
                                        continue

                                    if next_statement.type in (
                                        AST_STATEMENT.AST_STATEMENT_GOTO,
                                        AST_STATEMENT.AST_STATEMENT_BREAK,
                                    ):
                                        if (
                                            function.is_valid_label(
                                                next_statement.instruction.label
                                            )
                                            or next_statement.instruction.type
                                            != BC_OP.BC_OP_JMP
                                            or next_statement.instruction.target
                                            != function.labels[target_label].target
                                            or cur.assignment.expressions[-1].type
                                            != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                            or Ast.get_constant_type(
                                                cur.assignment.expressions[-1]
                                            )
                                            == CONSTANT_TYPE.INVALID_CONSTANT
                                        ):
                                            valid = False
                                            break

                                        constant_type = cur.assignment.expressions[
                                            -1
                                        ].constant.type
                                        if constant_type in (
                                            AST_CONSTANT.AST_CONSTANT_NIL,
                                            AST_CONSTANT.AST_CONSTANT_FALSE,
                                        ):
                                            node_type = ConditionNodeType.FALSY_TEST
                                        else:
                                            node_type = ConditionNodeType.TRUTHY_TEST
                                        condition_builder.add_node(
                                            node_type,
                                            cur.instruction.label,
                                            function.get_label_from_id(
                                                next_statement.instruction.target
                                            ),
                                            cur.assignment.expressions,
                                        )
                                        j += 1
                                        continue

                                    valid = False
                                    break

                                valid = False
                                break

                            if valid:
                                if not has_bool_construct:
                                    condition_builder.add_node(
                                        ConditionNodeType.TRUTHY_TEST,
                                        statement.instruction.label,
                                        target_label,
                                        statement.assignment.expressions,
                                    )
                                elif block[i - 3].type == AST_STATEMENT.AST_STATEMENT_GOTO:
                                    condition_builder.add_node(
                                        ConditionNodeType.TRUTHY_TEST,
                                        block[i - 4].instruction.label,
                                        target_label,
                                        block[i - 4].assignment.expressions,
                                    )

                                built_expression = condition_builder.build_condition()
                                if built_expression is not None:
                                    statement.assignment.expressions[-1] = built_expression
                                    for remove_index in range(index, i):
                                        remove_statement = block[remove_index]
                                        if (
                                            remove_statement.type
                                            == AST_STATEMENT.AST_STATEMENT_CONDITION
                                        ):
                                            if (
                                                remove_statement.instruction.target
                                                == function.labels[target_label].target
                                            ):
                                                slot_scope.usages -= 1
                                            function.remove_jump(
                                                remove_statement.instruction.id + 1,
                                                remove_statement.instruction.target,
                                            )
                                            if remove_statement.assignment.variables:
                                                function.remove_jump(
                                                    remove_statement.instruction.id,
                                                    remove_statement.instruction.id + 2,
                                                )
                                            continue
                                        if remove_statement.type in (
                                            AST_STATEMENT.AST_STATEMENT_GOTO,
                                            AST_STATEMENT.AST_STATEMENT_BREAK,
                                        ):
                                            function.remove_jump(
                                                remove_statement.instruction.id,
                                                remove_statement.instruction.target,
                                            )
                                            continue
                                        if (
                                            remove_statement.type
                                            == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                                        ):
                                            slot_scope.usages -= 1

                                    statement.instruction.label = block[index].instruction.label
                                    statement.assignment.is_table_constructor = False
                                    del block[index:i]
                                    i = index
                                    statement = block[i]
                        if debug_slot_case:
                            verbose_log(
                                "Debug function[42] slot final state: "
                                f"id={statement.instruction.id}, index={index}"
                            )

            if (
                i > 0
                and statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and len(statement.assignment.variables) == 1
                and statement.assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                and statement.assignment.variables[-1].table is not None
                and statement.assignment.variables[-1].table.type
                == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                and statement.assignment.variables[-1].table.variable.type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and not function.is_valid_label(statement.instruction.label)
                and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and len(block[i - 1].assignment.variables) == 1
                and block[i - 1].assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and block[i - 1].assignment.variables[-1].slot
                == statement.assignment.variables[-1].table.variable.slot
            ):
                previous_assignment = block[i - 1]
                table_variable = statement.assignment.variables[-1]

                if (
                    previous_assignment.assignment.is_table_constructor
                    and previous_assignment.assignment.expressions
                    and previous_assignment.assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_TABLE
                    and previous_assignment.assignment.expressions[-1].table.multres_field is None
                    and (
                        table_variable.is_multres
                        or Ast.get_constant_type(table_variable.table_index)
                        <= CONSTANT_TYPE.NIL_CONSTANT
                        or Ast.get_constant_type(statement.assignment.expressions[-1])
                        == CONSTANT_TYPE.INVALID_CONSTANT
                    )
                    and (
                        table_variable.is_multres
                        or not has_self_reference(
                            previous_assignment.assignment.variables[-1].slot,
                            table_variable.table_index,
                        )
                    )
                    and not has_self_reference(
                        previous_assignment.assignment.variables[-1].slot,
                        statement.assignment.expressions[-1],
                    )
                ):
                    table_expression = previous_assignment.assignment.expressions[-1]
                    if table_variable.is_multres:
                        table_expression.table.multres_index = table_variable.multres_index
                        table_expression.table.multres_field = statement.assignment.expressions[-1]
                    else:
                        if (
                            table_variable.table_index is not None
                            and table_variable.table_index.type
                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            and table_variable.table_index.constant.type
                            == AST_CONSTANT.AST_CONSTANT_STRING
                        ):
                            for j in range(len(table_expression.table.constants.fields) - 1, -1, -1):
                                key = table_expression.table.constants.fields[j].key
                                value = table_expression.table.constants.fields[j].value
                                if (
                                    key is None
                                    or key.type != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                    or key.constant.type != AST_CONSTANT.AST_CONSTANT_STRING
                                    or key.constant.string != table_variable.table_index.constant.string
                                ):
                                    continue
                                if (
                                    value is not None
                                    and value.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                    and value.constant.type == AST_CONSTANT.AST_CONSTANT_NIL
                                ):
                                    del table_expression.table.constants.fields[j]
                                break

                        table_expression.table.fields.append(
                            AstTableField(
                                key=table_variable.table_index,
                                value=statement.assignment.expressions[-1],
                            )
                        )

                    if previous_assignment.assignment.variables[-1].slot_scope is not None:
                        previous_assignment.assignment.variables[-1].slot_scope.scope.usages -= 1
                    del block[i]
                    i -= 1
                    continue

                if (
                    not table_variable.is_multres
                    and previous_assignment.assignment.variables[-1].slot_scope is not None
                    and previous_assignment.assignment.variables[-1].slot_scope.scope.usages == 1
                ):
                    table_variable.table = previous_assignment.assignment.expressions[-1]
                    function.slot_scope_collector.remove_scope(
                        previous_assignment.assignment.variables[-1].slot,
                        previous_assignment.assignment.variables[-1].slot_scope,
                    )
                    statement.instruction.label = previous_assignment.instruction.label
                    i -= 1
                    del block[i]
                    statement = block[i]

            i += 1

    def eliminate_conditions(
        self,
        function: Function,
        block: list[Statement],
        previous_block: Optional[BlockInfo],
    ) -> None:
        self._eliminate_assignment_test_copy_conditions(function, block, previous_block)
        self._fold_and_or_assignment_constructs(function, block, previous_block)

    def _eliminate_assignment_test_copy_conditions(
        self,
        function: Function,
        block: list[Statement],
        previous_block: Optional[BlockInfo],
    ) -> None:
        block_info = BlockInfo(block=block, previous_block=previous_block)
        expressions: list[Optional[Expression]] = [None]
        i = len(block) - 1

        while i >= 0:
            statement = block[i]
            if statement.instruction.id == INVALID_ID:
                i -= 1
                continue

            block_info.index = i
            target_label = Ast.get_label_from_next_statement(
                function, block_info, False, False
            )
            extended_target_label = Ast.get_label_from_next_statement(
                function, block_info, True, False
            )
            if (
                not function.is_valid_label(target_label)
                or function.labels[target_label].jump_ids[0] > statement.instruction.id
            ):
                i -= 1
                continue

            assignment_index = INVALID_ID

            if statement.type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                index = INVALID_ID
                for jump_id in reversed(function.labels[target_label].jump_ids):
                    if jump_id >= function.labels[target_label].target:
                        continue
                    index = Ast.get_block_index_from_id(block, jump_id - 1)
                    if index == INVALID_ID:
                        break

                    target_statement = block[index]
                    if target_statement.type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                        if not target_statement.assignment.variables:
                            if (
                                target_label == extended_target_label
                                or (
                                    len(target_statement.assignment.expressions) == 1
                                    and target_statement.assignment.expressions[-1].type
                                    == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                    and target_statement.assignment.expressions[-1]
                                    .variable.type
                                    == AST_VARIABLE.AST_VARIABLE_SLOT
                                )
                            ):
                                index = INVALID_ID
                                continue
                            index = INVALID_ID
                        break

                    if target_statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                        if (
                            index + 1 < len(block)
                            and block[index + 1].type
                            in (
                                AST_STATEMENT.AST_STATEMENT_GOTO,
                                AST_STATEMENT.AST_STATEMENT_BREAK,
                            )
                            and block[index + 1].instruction.type == BC_OP.BC_OP_JMP
                            and len(target_statement.assignment.variables) == 1
                            and target_statement.assignment.variables[-1].type
                            == AST_VARIABLE.AST_VARIABLE_SLOT
                            and target_statement.assignment.expressions
                            and target_statement.assignment.expressions[-1].type
                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            and Ast.get_constant_type(
                                target_statement.assignment.expressions[-1]
                            )
                            != CONSTANT_TYPE.INVALID_CONSTANT
                        ):
                            break

                    index = INVALID_ID
                    break

                if index == INVALID_ID:
                    i -= 1
                    continue
                assignment_index = index

            elif statement.type in (
                AST_STATEMENT.AST_STATEMENT_GOTO,
                AST_STATEMENT.AST_STATEMENT_BREAK,
            ):
                if (
                    i == 0
                    or function.is_valid_label(statement.instruction.label)
                    or statement.instruction.type != BC_OP.BC_OP_JMP
                    or statement.instruction.target != function.labels[target_label].target
                    or block[i - 1].type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    or len(block[i - 1].assignment.variables) != 1
                    or block[i - 1].assignment.variables[-1].type
                    != AST_VARIABLE.AST_VARIABLE_SLOT
                    or not block[i - 1].assignment.expressions
                    or block[i - 1].assignment.expressions[-1].type
                    != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                    or Ast.get_constant_type(block[i - 1].assignment.expressions[-1])
                    == CONSTANT_TYPE.INVALID_CONSTANT
                ):
                    i -= 1
                    continue
                assignment_index = i - 1

            elif statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                if (
                    len(statement.assignment.variables) != 1
                    or statement.assignment.variables[-1].type
                    != AST_VARIABLE.AST_VARIABLE_SLOT
                ):
                    i -= 1
                    continue
                assignment_index = i

            else:
                i -= 1
                continue

            index = assignment_index
            has_bool_construct = False

            if (
                i >= 3
                and statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and statement.assignment.expressions
                and statement.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                and statement.assignment.expressions[-1].constant.type
                == AST_CONSTANT.AST_CONSTANT_TRUE
                and block[i - 1].type
                in (
                    AST_STATEMENT.AST_STATEMENT_GOTO,
                    AST_STATEMENT.AST_STATEMENT_BREAK,
                )
                and not function.is_valid_label(block[i - 1].instruction.label)
                and block[i - 1].instruction.type == BC_OP.BC_OP_JMP
                and block[i - 1].instruction.target == function.labels[target_label].target
                and block[i - 2].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and block[i - 2].assignment.expressions
                and block[i - 2].assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                and block[i - 2].assignment.expressions[-1].constant.type
                == AST_CONSTANT.AST_CONSTANT_FALSE
                and len(block[i - 2].assignment.variables) == 1
                and block[i - 2].assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and block[i - 2].assignment.variables[-1].slot
                == block[assignment_index].assignment.variables[-1].slot
            ):
                if block[i - 3].type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                    if (
                        len(block[i - 3].assignment.expressions) == 2
                        and block[i - 3].instruction.target == block[i].instruction.id
                    ):
                        has_bool_construct = True
                elif block[i - 3].type in (
                    AST_STATEMENT.AST_STATEMENT_GOTO,
                    AST_STATEMENT.AST_STATEMENT_BREAK,
                ):
                    if (
                        i >= 4
                        and (
                            not function.is_valid_label(block[i - 3].instruction.label)
                            or (
                                function.labels[block[i - 3].instruction.label].jump_ids
                                and len(
                                    function.labels[block[i - 3].instruction.label].jump_ids
                                )
                                == 1
                                and block[i - 4].type
                                == AST_STATEMENT.AST_STATEMENT_CONDITION
                                and bool(block[i - 4].assignment.variables)
                            )
                        )
                        and block[i - 3].instruction.type == BC_OP.BC_OP_JMP
                        and block[i - 3].instruction.target
                        == function.labels[extended_target_label].target
                        and (
                            function.is_valid_label(block[i].instruction.label)
                            or function.is_valid_label(block[i - 2].instruction.label)
                        )
                    ):
                        has_bool_construct = True

                if has_bool_construct:
                    if (
                        (
                            function.is_valid_label(block[i].instruction.label)
                            and function.labels[block[i].instruction.label].jump_ids
                            and function.labels[block[i].instruction.label].jump_ids[-1]
                            >= block[i].instruction.id
                        )
                        or (
                            function.is_valid_label(block[i - 2].instruction.label)
                            and function.labels[block[i - 2].instruction.label].jump_ids
                            and function.labels[block[i - 2].instruction.label].jump_ids[-1]
                            >= block[i - 2].instruction.id
                        )
                    ):
                        i -= 1
                        continue

                    if function.is_valid_label(block[i].instruction.label):
                        for jump_id in reversed(
                            function.labels[block[i].instruction.label].jump_ids
                        ):
                            target_index = Ast.get_block_index_from_id(block, jump_id - 1)
                            if (
                                target_index == INVALID_ID
                                or block[target_index].type
                                != AST_STATEMENT.AST_STATEMENT_CONDITION
                                or bool(block[target_index].assignment.variables)
                            ):
                                index = INVALID_ID
                                break

                            if not block[target_index].assignment.expressions:
                                has_bool_construct = False
                                break

                    if has_bool_construct and function.is_valid_label(
                        block[i - 2].instruction.label
                    ):
                        for jump_id in reversed(
                            function.labels[block[i - 2].instruction.label].jump_ids
                        ):
                            target_index = Ast.get_block_index_from_id(block, jump_id - 1)
                            if (
                                target_index == INVALID_ID
                                or block[target_index].type
                                != AST_STATEMENT.AST_STATEMENT_CONDITION
                            ):
                                index = INVALID_ID
                                break

                            if (
                                not block[target_index].assignment.expressions
                                or bool(block[target_index].assignment.variables)
                            ):
                                has_bool_construct = False
                                break

                    if index == INVALID_ID:
                        i -= 1
                        continue

            previous_valid_index = INVALID_ID
            has_end_assignment = (
                (
                    block[i - 3].type == AST_STATEMENT.AST_STATEMENT_CONDITION
                    or block[i - 4].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                )
                if has_bool_construct
                else statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
            )
            target_index = (
                (
                    i - (4 if has_end_assignment else 3)
                    if block[i - 3].type == AST_STATEMENT.AST_STATEMENT_GOTO
                    else i - 2
                )
                if has_bool_construct
                else (i if has_end_assignment else i + 1)
            )

            for jump_id in reversed(function.labels[target_label].jump_ids):
                if jump_id > statement.instruction.id:
                    continue

                if jump_id < block[index].instruction.id:
                    index = Ast.get_block_index_from_id(block, jump_id - 1)

                    if (
                        has_bool_construct
                        and index == i - 2
                        and not function.is_valid_label(block[i].instruction.label)
                    ):
                        index = Ast.get_block_index_from_id(
                            block,
                            function.labels[block[i - 2].instruction.label].jump_ids[0]
                            - 1,
                        )
                        if index == INVALID_ID:
                            index = i - 2

                k = i
                while index != INVALID_ID and block[index].instruction.id < block[k].instruction.id:
                    if function.is_valid_label(block[k].instruction.label):
                        if (
                            function.labels[block[k].instruction.label].jump_ids
                            and function.labels[block[k].instruction.label].jump_ids[-1]
                            >= block[k].instruction.id
                        ):
                            index = INVALID_ID
                            break

                        while (
                            function.labels[block[k].instruction.label].jump_ids
                            and function.labels[block[k].instruction.label].jump_ids[0]
                            < block[index].instruction.id
                        ):
                            if index == 0:
                                index = INVALID_ID
                                break
                            index -= 1
                    k -= 1

                if index == INVALID_ID:
                    break

                if block[index].type in (
                    AST_STATEMENT.AST_STATEMENT_GOTO,
                    AST_STATEMENT.AST_STATEMENT_BREAK,
                ) and block[index].instruction.target == function.labels[target_label].target:
                    if index:
                        index -= 1

                valid_window = True
                k = index
                while k < target_index:
                    current = block[k]
                    if current.type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                        if current.assignment.variables:
                            if (
                                current.instruction.target
                                == function.labels[target_label].target
                                and current.assignment.variables[-1].slot
                                == block[assignment_index].assignment.variables[-1].slot
                            ):
                                k += 1
                                continue
                        elif (
                            current.instruction.target
                            == function.labels[target_label].target
                            and len(current.assignment.expressions) == 1
                            and current.assignment.expressions[-1].type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and current.assignment.expressions[-1].variable.type
                            == AST_VARIABLE.AST_VARIABLE_SLOT
                            and current.assignment.expressions[-1].variable.slot
                            == block[assignment_index].assignment.variables[-1].slot
                        ):
                            k += 1
                            continue
                        elif (
                            (
                                current.instruction.target
                                == function.labels[extended_target_label].target
                                and not has_end_assignment
                            )
                            or (
                                current.instruction.target > current.instruction.id
                                and current.instruction.target
                                < function.labels[target_label].target
                            )
                        ):
                            k += 1
                            continue

                        valid_window = False
                        break

                    if current.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                        if (
                            len(current.assignment.variables) == 1
                            and current.assignment.variables[-1].type
                            == AST_VARIABLE.AST_VARIABLE_SLOT
                            and current.assignment.variables[-1].slot
                            == block[assignment_index].assignment.variables[-1].slot
                            and current.assignment.expressions
                            and current.assignment.expressions[-1].type
                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            and Ast.get_constant_type(current.assignment.expressions[-1])
                            != CONSTANT_TYPE.INVALID_CONSTANT
                        ):
                            k += 1
                            if (
                                k != target_index
                                and block[k].type
                                in (
                                    AST_STATEMENT.AST_STATEMENT_GOTO,
                                    AST_STATEMENT.AST_STATEMENT_BREAK,
                                )
                                and not function.is_valid_label(block[k].instruction.label)
                                and block[k].instruction.type == BC_OP.BC_OP_JMP
                                and block[k].instruction.target
                                == function.labels[target_label].target
                            ):
                                k += 1
                                continue
                        valid_window = False
                        break

                    valid_window = False
                    break

                if not valid_window:
                    index = INVALID_ID
                    break

                previous_valid_index = index

            if previous_valid_index == INVALID_ID:
                i -= 1
                continue
            index = previous_valid_index

            condition_builder = ConditionBuilder(
                ConditionBuilderType.ASSIGNMENT,
                self,
                target_label,
                block[i].instruction.label if has_bool_construct else INVALID_ID,
                block[i - 2].instruction.label if has_bool_construct else INVALID_ID,
            )

            j = index
            while j < target_index:
                current = block[j]
                if current.type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                    use_direct_target = (
                        has_end_assignment
                        or bool(current.assignment.variables)
                        or (
                            (
                                current.instruction.target
                                == function.labels[target_label].target
                            )
                            and (
                                target_label != extended_target_label
                                or (
                                    len(current.assignment.expressions) == 1
                                    and current.assignment.expressions[-1].type
                                    == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                    and current.assignment.expressions[-1].variable.type
                                    == AST_VARIABLE.AST_VARIABLE_SLOT
                                    and current.assignment.expressions[-1].variable.slot
                                    == block[assignment_index].assignment.variables[-1].slot
                                )
                            )
                            or (
                                current.instruction.target
                                != function.labels[extended_target_label].target
                            )
                        )
                    )
                    current_target_label = (
                        function.get_label_from_id(current.instruction.target)
                        if use_direct_target
                        else len(function.labels)
                    )
                    condition_builder.add_node(
                        condition_builder.get_node_type(
                            current.instruction.type, current.condition.swapped
                        ),
                        current.instruction.label,
                        current_target_label,
                        current.assignment.expressions,
                        has_alternate_target=(
                            current.instruction.target == function.labels[target_label].target
                            and not has_end_assignment
                            and len(current.assignment.expressions) == 1
                            and current.assignment.expressions[-1].type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and current.assignment.expressions[-1].variable.type
                            == AST_VARIABLE.AST_VARIABLE_SLOT
                            and current.assignment.expressions[-1].variable.slot
                            == block[assignment_index].assignment.variables[-1].slot
                            and target_label == extended_target_label
                        ),
                    )
                    j += 1
                    continue

                if current.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                    constant_type = current.assignment.expressions[-1].constant.type
                    if constant_type in (
                        AST_CONSTANT.AST_CONSTANT_NIL,
                        AST_CONSTANT.AST_CONSTANT_FALSE,
                    ):
                        node_type = ConditionNodeType.FALSY_TEST
                    else:
                        node_type = ConditionNodeType.TRUTHY_TEST
                    condition_builder.add_node(
                        node_type,
                        current.instruction.label,
                        function.get_label_from_id(block[j + 1].instruction.target),
                        current.assignment.expressions,
                    )
                    j += 2
                    continue

                j += 1

            if has_end_assignment:
                if not has_bool_construct:
                    condition_builder.add_node(
                        ConditionNodeType.TRUTHY_TEST,
                        block[i].instruction.label,
                        target_label,
                        block[i].assignment.expressions,
                    )
                elif block[i - 3].type == AST_STATEMENT.AST_STATEMENT_GOTO:
                    condition_builder.add_node(
                        ConditionNodeType.TRUTHY_TEST,
                        block[i - 4].instruction.label,
                        target_label,
                        block[i - 4].assignment.expressions,
                    )
            else:
                expressions[-1] = self.new_slot(
                    block[assignment_index].assignment.variables[-1].slot
                )
                expressions[-1].variable.slot_scope = block[assignment_index].assignment.variables[
                    -1
                ].slot_scope
                condition_builder.add_node(
                    ConditionNodeType.TRUTHY_TEST,
                    len(function.labels),
                    target_label,
                    expressions,
                )

            expressions[-1] = condition_builder.build_condition()
            if expressions[-1] is None:
                i -= 1
                continue
            block[assignment_index].assignment.expressions[-1] = expressions[-1]

            for j in range(index, i + 1):
                current = block[j]
                if current.type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                    function.remove_jump(
                        current.instruction.id + 1, current.instruction.target
                    )
                    if not current.assignment.variables:
                        continue
                    function.remove_jump(
                        current.instruction.id, current.instruction.id + 2
                    )
                    # fall through to ASSIGNMENT scope merge below

                if current.type in (
                    AST_STATEMENT.AST_STATEMENT_CONDITION,
                    AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                ):
                    base_var = block[assignment_index].assignment.variables[-1]
                    cur_var = current.assignment.variables[-1]
                    if (
                        base_var.slot_scope is not None
                        and cur_var.slot_scope is not None
                        and cur_var.slot_scope.scope is not base_var.slot_scope.scope
                    ):
                        base_scope = base_var.slot_scope.scope
                        merged_scope = cur_var.slot_scope.scope
                        base_scope.usages += merged_scope.usages
                        if merged_scope.scope_begin < base_scope.scope_begin:
                            base_scope.scope_begin = merged_scope.scope_begin
                        if merged_scope.scope_end > base_scope.scope_end:
                            base_scope.scope_end = merged_scope.scope_end
                        cur_var.slot_scope.scope = base_scope
                        if cur_var.slot_scope is not base_var.slot_scope:
                            function.slot_scope_collector.remove_scope(
                                cur_var.slot, cur_var.slot_scope
                            )
                    continue

                if current.type in (
                    AST_STATEMENT.AST_STATEMENT_GOTO,
                    AST_STATEMENT.AST_STATEMENT_BREAK,
                ):
                    function.remove_jump(
                        current.instruction.id, current.instruction.target
                    )
                    continue

            block[i] = block[assignment_index]
            block[i].type = AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
            block[i].instruction.label = block[index].instruction.label
            if (
                block[i].assignment.variables[-1].slot_scope is not None
                and block[i].assignment.variables[-1].slot_scope.scope.scope_begin
                >= block[index].instruction.id
            ):
                block[i].assignment.forward_declaration = True
            del block[index:i]
            i = index
            i -= 1

    def _fold_and_or_assignment_constructs(
        self,
        function: Function,
        block: list[Statement],
        previous_block: Optional[BlockInfo],
    ) -> None:
        def maybe_split_false_jmp_condition(index: int) -> int:
            if (
                index <= 0
                or index >= len(block)
                or block[index].type != AST_STATEMENT.AST_STATEMENT_CONDITION
                or block[index].instruction.type != BC_OP.BC_OP_JMP
                or not block[index].assignment.expressions
                or block[index].assignment.expressions[-1].type
                != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                or block[index].assignment.expressions[-1].constant.type
                != AST_CONSTANT.AST_CONSTANT_FALSE
                or function.is_valid_label(block[index].instruction.label)
                or block[index - 1].type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or len(block[index - 1].assignment.variables) != 1
                or block[index - 1].assignment.variables[-1].type
                != AST_VARIABLE.AST_VARIABLE_SLOT
                or len(block[index - 1].assignment.expressions) != 1
                or Ast.get_constant_type(block[index - 1].assignment.expressions[-1])
                == CONSTANT_TYPE.INVALID_CONSTANT
            ):
                return index

            function.remove_jump(
                block[index].instruction.id, block[index].instruction.target
            )
            block[index].assignment.expressions.clear()
            block[index].type = AST_STATEMENT.AST_STATEMENT_GOTO

            synthetic_goto = self.new_statement(AST_STATEMENT.AST_STATEMENT_GOTO)
            block.insert(index, synthetic_goto)
            block[index].instruction.type = BC_OP.BC_OP_JMP
            block[index].instruction.id = block[index + 1].instruction.id
            block[index + 1].instruction.id += 1
            block[index].instruction.target = block[index + 1].instruction.id
            function.add_jump(block[index].instruction.id, block[index].instruction.target)
            function.add_jump(
                block[index + 1].instruction.id, block[index + 1].instruction.target
            )
            block[index + 1].instruction.label = function.get_label_from_id(
                block[index + 1].instruction.id
            )

            return index + 1

        block_info = BlockInfo(block=block, previous_block=previous_block)
        i = len(block) - 1
        while i >= 0:
            t = block[i].type
            if t == AST_STATEMENT.AST_STATEMENT_CONDITION:
                block_info.index = i
                target_label = Ast.get_label_from_next_statement(function, block_info, True, False)
                target_index = INVALID_ID
                index = i

                while index and block[index - 1].type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                    index -= 1

                j = index
                while j <= i:
                    if function.is_valid_label(block[j].instruction.label):
                        label_info = function.labels[block[j].instruction.label]
                        if (
                            label_info.jump_ids[0] < block[index].instruction.id
                            or label_info.jump_ids[-1] > block[j].instruction.id
                        ):
                            index = j
                            target_index = INVALID_ID
                        elif (
                            j
                            and j - 1 >= index
                            and block[j - 1].instruction.target == label_info.target
                        ):
                            k = index
                            while (
                                k < j
                                and block[k].instruction.target > block[k].instruction.id
                                and block[k].instruction.target <= block[j].instruction.id
                            ):
                                if k == j - 1:
                                    index = j
                                    target_index = INVALID_ID
                                    break
                                k += 1

                    if (
                        (target_label == INVALID_ID or block[j].instruction.target != function.labels[target_label].target)
                        and (
                            block[j].instruction.target < block[j].instruction.id
                            or block[j].instruction.target > block[i].instruction.id
                        )
                    ):
                        if target_index != INVALID_ID:
                            if block[j].instruction.target == block[target_index].instruction.target:
                                j += 1
                                continue
                            index = target_index + 1
                            j = target_index
                            target_index = INVALID_ID
                            j += 1
                            continue
                        target_index = j
                    j += 1

                if target_index == INVALID_ID:
                    extended_target_label = target_label
                    target_label = INVALID_ID
                else:
                    extended_target_label = function.get_label_from_id(
                        block[target_index].instruction.target
                    )

                condition_builder = ConditionBuilder(
                    ConditionBuilderType.STATEMENT,
                    self,
                    INVALID_ID,
                    target_label,
                    extended_target_label,
                )

                for j in range(index, i + 1):
                    if block[j].assignment.variables:
                        can_downgrade_copy_test = (
                            len(block[j].assignment.variables) == 1
                            and len(block[j].assignment.expressions) == 1
                            and block[j].assignment.variables[-1].type
                            == AST_VARIABLE.AST_VARIABLE_SLOT
                            and block[j].instruction.type
                            in (BC_OP.BC_OP_ISTC, BC_OP.BC_OP_ISFC)
                        )
                        if can_downgrade_copy_test:
                            copy_var = block[j].assignment.variables[-1]
                            if copy_var.slot_scope is not None:
                                function.slot_scope_collector.remove_scope(
                                    copy_var.slot, copy_var.slot_scope
                                )
                            function.remove_jump(
                                block[j].instruction.id, block[j].instruction.id + 2
                            )
                            if block[j].instruction.type == BC_OP.BC_OP_ISTC:
                                block[j].instruction.type = BC_OP.BC_OP_IST
                            else:
                                block[j].instruction.type = BC_OP.BC_OP_ISF
                            block[j].assignment.variables.clear()
                        else:
                            decompiler_assert(
                                False,
                                "Failed to eliminate all test and copy conditions",
                                self.bytecode.file_path,
                                "Ast::eliminate_conditions",
                                __file__,
                                0,
                            )
                    condition_builder.add_node(
                        condition_builder.get_node_type(
                            block[j].instruction.type, block[j].condition.swapped
                        ),
                        block[j].instruction.label,
                        function.get_label_from_id(block[j].instruction.target),
                        block[j].assignment.expressions,
                    )

                built_condition = condition_builder.build_condition()
                decompiler_assert(
                    built_condition is not None,
                    "Failed to build condition",
                    self.bytecode.file_path,
                    "Ast::eliminate_conditions",
                    __file__,
                    0,
                )
                block[i].assignment.expressions = [built_condition]

                for j in range(index, i + 1):
                    function.remove_jump(
                        block[j].instruction.id + 1, block[j].instruction.target
                    )

                decompiler_assert(
                    extended_target_label != INVALID_ID
                    and 0 <= extended_target_label < len(function.labels),
                    "Failed to resolve condition target label",
                    self.bytecode.file_path,
                    "Ast::eliminate_conditions",
                    __file__,
                    0,
                )
                block[i].instruction.target = function.labels[extended_target_label].target
                function.add_jump(block[i].instruction.id, block[i].instruction.target)
                block[i].instruction.label = block[index].instruction.label
                del block[index:i]
                i = index

                i = maybe_split_false_jmp_condition(i)
                i -= 1
                continue

            if t in (
                AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR,
                AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
            ):
                self.eliminate_conditions(function, block[i].block, None)
                i -= 1
                continue

            if t in (
                AST_STATEMENT.AST_STATEMENT_LOOP,
                AST_STATEMENT.AST_STATEMENT_DECLARATION,
            ):
                block_info.index = i
                self.eliminate_conditions(function, block[i].block, block_info)
                i -= 1
                continue

            i -= 1
        self.build_multi_assignment(function, block)

    def build_multi_assignment(self, function: Function, block: list[Statement]) -> None:
        def is_table_index_or_const_index_variable(variable: AstVariable) -> bool:
            if variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                return False
            if (
                variable.table is None
                or variable.table.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                or variable.table.variable.type != AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                return False
            ct = Ast.get_constant_type(variable.table_index)
            if ct != CONSTANT_TYPE.INVALID_CONSTANT:
                return True
            return (
                variable.table_index.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                and variable.table_index.variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
            )

        i = len(block) - 1
        while i >= 0:
            t = block[i].type
            _did_multi_var_merge = False
            if t == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                if len(block[i].assignment.variables) >= 2:
                    if i + len(block[i].assignment.variables) >= len(block):
                        i -= 1
                        continue
                    is_multi_assignment = True

                    j = len(block[i].assignment.variables) - 1
                    while j >= 0:
                        target_index = i + len(block[i].assignment.variables) - j
                        target_stmt = block[target_index]
                        var_j = block[i].assignment.variables[j]
                        cond = (
                            var_j.slot_scope is not None
                            and var_j.slot_scope.scope.usages == 1
                            and not function.is_valid_label(target_stmt.instruction.label)
                            and target_stmt.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                            and len(target_stmt.assignment.variables) == 1
                            and (
                                target_stmt.assignment.variables[-1].type
                                != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                                or is_table_index_or_const_index_variable(
                                    target_stmt.assignment.variables[-1]
                                )
                            )
                            and len(target_stmt.assignment.expressions) == 1
                            and target_stmt.assignment.expressions[-1].type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and target_stmt.assignment.expressions[-1].variable.type
                            == AST_VARIABLE.AST_VARIABLE_SLOT
                            and target_stmt.assignment.expressions[-1].variable.slot_scope
                            == var_j.slot_scope
                        )
                        if not cond:
                            is_multi_assignment = False
                            break
                        j -= 1

                    if not is_multi_assignment:
                        i -= 1
                        continue

                    j = len(block[i].assignment.variables) - 1
                    while j >= 0:
                        var_j = block[i].assignment.variables[j]
                        if var_j.slot_scope is not None:
                            function.slot_scope_collector.remove_scope(var_j.slot, var_j.slot_scope)
                        block[i].assignment.variables[j] = block[i + 1].assignment.variables[-1]
                        del block[i + 1]
                        j -= 1
                    # Continue with post-merge folding.
                    _did_multi_var_merge = True

            if not _did_multi_var_merge:
                if t not in (
                    AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                    AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL,
                ):
                    i -= 1
                    continue

                if t == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT and not block[i].assignment.variables:
                    i -= 1
                    continue

                index = i
                if (
                    block[i].type == AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL
                    or (
                        block[i].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                        and block[i].assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                        and block[i].assignment.variables[-1].slot_scope is not None
                        and not block[i].assignment.variables[-1].slot_scope.scope.usages
                        and not block[i].assignment.forward_declaration
                    )
                ):
                    while (
                        index
                        and not function.is_valid_label(block[index].instruction.label)
                        and block[index - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                        and len(block[index - 1].assignment.variables) == 1
                        and block[index - 1].assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                        and block[index - 1].assignment.variables[-1].slot_scope is not None
                        and not block[index - 1].assignment.variables[-1].slot_scope.scope.usages
                        and not block[index - 1].assignment.forward_declaration
                    ):
                        index -= 1

                if (
                    index
                    and i + 1 < len(block)
                    and not function.is_valid_label(block[index].instruction.label)
                    and not function.is_valid_label(block[i + 1].instruction.label)
                    and block[index - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(block[index - 1].assignment.variables) == 1
                    and block[index - 1].assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[index - 1].assignment.variables[-1].slot_scope is not None
                    and block[index - 1].assignment.variables[-1].slot_scope.scope.usages == 1
                    and block[i + 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(block[i + 1].assignment.variables) == 1
                    and (
                        block[i + 1].assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                        or is_table_index_or_const_index_variable(block[i + 1].assignment.variables[-1])
                    )
                    and len(block[i + 1].assignment.expressions) == 1
                    and block[i + 1].assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and block[i + 1].assignment.expressions[-1].variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
                    and block[i + 1].assignment.expressions[-1].variable.slot_scope
                    == block[index - 1].assignment.variables[-1].slot_scope
                ):
                    if block[i].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                        last_var = block[i].assignment.variables[-1]
                        if last_var.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                            if (
                                last_var.slot_scope is not None
                                and not last_var.slot_scope.scope.usages
                                and not block[i].assignment.forward_declaration
                            ):
                                function.slot_scope_collector.remove_scope(
                                    last_var.slot, last_var.slot_scope
                                )
                                block[i].assignment.variables.clear()
                        elif last_var.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                            if (
                                index == i
                                and (
                                    last_var.table.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                    or last_var.table.variable.type != AST_VARIABLE.AST_VARIABLE_SLOT
                                    or (
                                        Ast.get_constant_type(last_var.table_index)
                                        == CONSTANT_TYPE.INVALID_CONSTANT
                                        and (
                                            last_var.table_index.type
                                            != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                            or last_var.table_index.variable.type
                                            != AST_VARIABLE.AST_VARIABLE_SLOT
                                        )
                                    )
                                )
                            ):
                                i -= 1
                                continue
                    else:
                        block[i].type = AST_STATEMENT.AST_STATEMENT_ASSIGNMENT

                    while i != index:
                        i -= 1
                        prev_var = block[i].assignment.variables[-1]
                        if prev_var.slot_scope is not None:
                            function.slot_scope_collector.remove_scope(prev_var.slot, prev_var.slot_scope)
                        block[i + 1].assignment.expressions.insert(0, block[i].assignment.expressions[-1])
                        del block[i]
                    # fallthrough to post-merge folding
                else:
                    if (
                        block[i].type == AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL
                        and block[i].assignment.expressions
                        and block[i].assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_VARARG
                    ):
                        decompiler_assert(
                            i > 0
                            and not function.is_valid_label(block[i].instruction.label)
                            and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                            and len(block[i - 1].assignment.variables) == 1,
                            "Unable to eliminate vararg with zero returns",
                            self.bytecode.file_path,
                            "Ast::build_multi_assignment",
                            __file__,
                            0,
                        )
                        block[i - 1].assignment.expressions.append(block[i].assignment.expressions[-1])
                        del block[i]
                        i -= 1
                        i -= 1
                        continue
                    else:
                        i -= 1
                        continue

            while (
                i > 0
                and i + 1 < len(block)
                and not function.is_valid_label(block[i].instruction.label)
                and not function.is_valid_label(block[i + 1].instruction.label)
                and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and len(block[i - 1].assignment.variables) == 1
                and block[i - 1].assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                and block[i - 1].assignment.variables[-1].slot_scope is not None
                and block[i - 1].assignment.variables[-1].slot_scope.scope.usages == 1
                and block[i + 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and len(block[i + 1].assignment.variables) == 1
                and (
                    block[i + 1].assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                    or is_table_index_or_const_index_variable(block[i + 1].assignment.variables[-1])
                )
                and len(block[i + 1].assignment.expressions) == 1
                and block[i + 1].assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                and block[i + 1].assignment.expressions[-1].variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
                and block[i + 1].assignment.expressions[-1].variable.slot_scope
                == block[i - 1].assignment.variables[-1].slot_scope
            ):
                prev_var = block[i - 1].assignment.variables[-1]
                function.slot_scope_collector.remove_scope(prev_var.slot, prev_var.slot_scope)
                block[i].assignment.expressions.insert(0, block[i - 1].assignment.expressions[-1])
                block[i].assignment.variables.insert(0, block[i + 1].assignment.variables[-1])
                block[i].instruction.label = block[i - 1].instruction.label
                del block[i - 1]
                del block[i]
                i -= 1

            j = len(block[i].assignment.variables) - 1
            while (
                j >= 0
                and i > 0
                and not function.is_valid_label(block[i].instruction.label)
                and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and len(block[i - 1].assignment.variables) == 1
                and block[i - 1].assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                and block[i - 1].assignment.variables[-1].slot_scope is not None
                and block[i - 1].assignment.variables[-1].slot_scope.scope.usages == 1
            ):
                if block[i].assignment.variables[j].type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    j -= 1
                    continue

                var_j = block[i].assignment.variables[j]
                if (
                    var_j.table_index.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and var_j.table_index.variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
                    and var_j.table_index.variable.slot_scope
                    == block[i - 1].assignment.variables[-1].slot_scope
                ):
                    prev_var = block[i - 1].assignment.variables[-1]
                    function.slot_scope_collector.remove_scope(prev_var.slot, prev_var.slot_scope)
                    var_j.table_index = block[i - 1].assignment.expressions[-1]
                    block[i].instruction.label = block[i - 1].instruction.label
                    i -= 1
                    del block[i]
                    j += 1
                    continue

                if (
                    var_j.table.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and var_j.table.variable.slot_scope
                    == block[i - 1].assignment.variables[-1].slot_scope
                ):
                    prev_var = block[i - 1].assignment.variables[-1]
                    function.slot_scope_collector.remove_scope(prev_var.slot, prev_var.slot_scope)
                    var_j.table = block[i - 1].assignment.expressions[-1]
                    block[i].instruction.label = block[i - 1].instruction.label
                    i -= 1
                    del block[i]
                    continue
                j -= 1

            i -= 1

        # Preserve the established post-multi-assignment normalization order.

    def _fold_if_not_assignment_to_or(
        self, function: Function, block: list[Statement]
    ) -> None:
        for statement in block:
            if statement.block:
                self._fold_if_not_assignment_to_or(function, statement.block)

        i = 0
        while i < len(block):
            statement = block[i]
            if (
                statement.type != AST_STATEMENT.AST_STATEMENT_IF
                or i + 1 < len(block)
                and block[i + 1].type == AST_STATEMENT.AST_STATEMENT_ELSE
                or len(statement.assignment.expressions) != 1
            ):
                i += 1
                continue

            condition = statement.assignment.expressions[-1]
            if (
                condition.type != AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION
                or condition.unary_operation.type != AST_UNARY_OPERATION.AST_UNARY_NOT
                or condition.unary_operation.operand is None
                or condition.unary_operation.operand.type
                != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                or condition.unary_operation.operand.variable.type
                != AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                i += 1
                continue

            candidates = [
                s for s in statement.block if s.type != AST_STATEMENT.AST_STATEMENT_EMPTY
            ]
            if len(candidates) != 1:
                i += 1
                continue

            assign = candidates[0]
            if (
                assign.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or len(assign.assignment.variables) != 1
                or assign.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
                or len(assign.assignment.expressions) != 1
                or assign.assignment.variables[-1].slot
                != condition.unary_operation.operand.variable.slot
            ):
                i += 1
                continue

            replacement = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION)
            replacement.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_OR
            replacement.binary_operation.left_operand = condition.unary_operation.operand
            replacement.binary_operation.right_operand = assign.assignment.expressions[-1]

            assign.assignment.expressions[-1] = replacement
            assign.instruction.label = statement.instruction.label
            function.remove_jump(statement.instruction.id, statement.instruction.target)
            block[i] = assign
            i += 1

    def _merge_declaration_or_assignment(self, block: list[Statement]) -> None:
        for statement in block:
            if statement.block:
                self._merge_declaration_or_assignment(statement.block)

        i = 0
        while i + 1 < len(block):
            declaration = block[i]
            assignment = block[i + 1]
            if (
                declaration.type != AST_STATEMENT.AST_STATEMENT_DECLARATION
                or assignment.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or len(declaration.assignment.variables) != 1
                or len(declaration.assignment.expressions) != 1
                or len(assignment.assignment.variables) != 1
                or len(assignment.assignment.expressions) != 1
                or declaration.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
                or assignment.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
                or declaration.assignment.variables[-1].slot
                != assignment.assignment.variables[-1].slot
                or assignment.assignment.expressions[-1].type
                != AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                or assignment.assignment.expressions[-1].binary_operation.type
                != AST_BINARY_OPERATION.AST_BINARY_OR
            ):
                i += 1
                continue

            left_operand = assignment.assignment.expressions[-1].binary_operation.left_operand
            if (
                left_operand.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                or left_operand.variable.type != AST_VARIABLE.AST_VARIABLE_SLOT
                or left_operand.variable.slot != declaration.assignment.variables[-1].slot
            ):
                i += 1
                continue

            assignment.assignment.expressions[-1].binary_operation.left_operand = (
                declaration.assignment.expressions[-1]
            )
            declaration.assignment.expressions[-1] = assignment.assignment.expressions[-1]
            del block[i + 1]

    def _post_clean_up_simplify_block(
        self, function: Function, block: list[Statement]
    ) -> None:
        for statement in block:
            if statement.block:
                self._post_clean_up_simplify_block(function, statement.block)

        j = 0
        while j < len(block):
            if (
                block[j].type == AST_STATEMENT.AST_STATEMENT_EMPTY
                and not function.is_valid_label(block[j].instruction.label)
            ):
                del block[j]
                continue
            j += 1

        def expression_slot_use_count(
            expression: Optional[Expression],
            slot: int,
            target_scope: Optional[ScopeCell],
        ) -> int:
            if expression is None:
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
                variable = expression.variable
                if variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    if variable.slot != slot:
                        return 0
                    if target_scope is None:
                        return 1
                    return 1 if variable.slot_scope is target_scope else 0
                if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    return expression_slot_use_count(
                        variable.table, slot, target_scope
                    ) + expression_slot_use_count(
                        variable.table_index, slot, target_scope
                    )
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
                function_call = expression.function_call
                uses = expression_slot_use_count(function_call.function, slot, target_scope)
                uses += expression_slot_use_count(
                    function_call.multres_argument, slot, target_scope
                )
                for argument in function_call.arguments:
                    uses += expression_slot_use_count(argument, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
                table = expression.table
                uses = expression_slot_use_count(table.multres_field, slot, target_scope)
                for field in table.fields:
                    uses += expression_slot_use_count(field.key, slot, target_scope)
                    uses += expression_slot_use_count(field.value, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
                binary_operation = expression.binary_operation
                return expression_slot_use_count(
                    binary_operation.left_operand, slot, target_scope
                ) + expression_slot_use_count(
                    binary_operation.right_operand, slot, target_scope
                )
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
                return expression_slot_use_count(
                    expression.unary_operation.operand, slot, target_scope
                )
            return 0

        def statement_slot_use_count(
            statement: Statement, slot: int, target_scope: Optional[ScopeCell]
        ) -> int:
            uses = expression_slot_use_count(
                statement.assignment.multres_return, slot, target_scope
            )
            for expression in statement.assignment.expressions:
                uses += expression_slot_use_count(expression, slot, target_scope)
            for variable in statement.assignment.variables:
                if variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    continue
                uses += expression_slot_use_count(variable.table, slot, target_scope)
                uses += expression_slot_use_count(
                    variable.table_index, slot, target_scope
                )
            for nested_statement in statement.block:
                uses += statement_slot_use_count(nested_statement, slot, target_scope)
            return uses

        def clone_statement_preserving_scopes(statement: Statement) -> Statement:
            # Keep scope-cell identity stable for scope-aware slot replacement.
            memo: dict[int, object] = {}

            for info in function.slot_scope_collector.slot_infos:
                if info.active_slot_scope is not None:
                    memo[id(info.active_slot_scope)] = info.active_slot_scope
                    if info.active_slot_scope.scope is not None:
                        memo[id(info.active_slot_scope.scope)] = info.active_slot_scope.scope

                for cell in info.slot_scopes:
                    memo[id(cell)] = cell
                    if cell.scope is not None:
                        memo[id(cell.scope)] = cell.scope

            for upvalue in function.upvalues:
                if upvalue.slot_scope is None:
                    continue
                memo[id(upvalue.slot_scope)] = upvalue.slot_scope
                if upvalue.slot_scope.scope is not None:
                    memo[id(upvalue.slot_scope.scope)] = upvalue.slot_scope.scope

            return copy.deepcopy(statement, memo)

        def get_single_assignment_from_branch(
            branch_statement: Statement,
        ) -> Optional[Statement]:
            if branch_statement.type not in (
                AST_STATEMENT.AST_STATEMENT_IF,
                AST_STATEMENT.AST_STATEMENT_ELSE,
            ):
                return None
            candidates = [
                statement
                for statement in branch_statement.block
                if statement.type != AST_STATEMENT.AST_STATEMENT_EMPTY
            ]
            if len(candidates) != 1:
                return None
            candidate = candidates[0]
            if (
                candidate.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or len(candidate.assignment.variables) != 1
                or len(candidate.assignment.expressions) != 1
                or candidate.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                return None
            return candidate

        def get_if_else_pair(
            start_index: int,
        ) -> Optional[tuple[Statement, Statement, bool]]:
            if start_index >= len(block) or block[start_index].type != AST_STATEMENT.AST_STATEMENT_IF:
                return None

            if (
                start_index + 1 < len(block)
                and block[start_index + 1].type == AST_STATEMENT.AST_STATEMENT_ELSE
            ):
                return block[start_index], block[start_index + 1], True

            if (
                len(block[start_index].block) >= 2
                and block[start_index].block[0].type == AST_STATEMENT.AST_STATEMENT_IF
                and block[start_index].block[1].type == AST_STATEMENT.AST_STATEMENT_ELSE
            ):
                return block[start_index].block[0], block[start_index].block[1], False

            return None

        def is_pure_expression(expression: Optional[Expression]) -> bool:
            if expression is None:
                return False
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT:
                return True
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
                variable = expression.variable
                if variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    return True
                if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    return is_pure_expression(variable.table) and is_pure_expression(
                        variable.table_index
                    )
                return False
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
                return is_pure_expression(
                    expression.binary_operation.left_operand
                ) and is_pure_expression(expression.binary_operation.right_operand)
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
                return is_pure_expression(expression.unary_operation.operand)
            return False

        def rewrite_and_comparison_expression(expression: Expression) -> Expression:
            if expression.type != AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
                return expression

            comparison_type = expression.binary_operation.type
            if comparison_type not in (
                AST_BINARY_OPERATION.AST_BINARY_LESS_THAN,
                AST_BINARY_OPERATION.AST_BINARY_LESS_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_GREATER_THEN,
                AST_BINARY_OPERATION.AST_BINARY_GREATER_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_NOT_EQUAL,
            ):
                return expression

            left_operand = expression.binary_operation.left_operand
            if (
                left_operand is None
                or left_operand.type != AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                or left_operand.binary_operation.type != AST_BINARY_OPERATION.AST_BINARY_AND
            ):
                return expression

            rewritten_comparison = self.new_expression(
                AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
            )
            rewritten_comparison.binary_operation.type = comparison_type
            rewritten_comparison.binary_operation.left_operand = self._clone_expression_deep(
                left_operand.binary_operation.right_operand
            )
            rewritten_comparison.binary_operation.right_operand = self._clone_expression_deep(
                expression.binary_operation.right_operand
            )

            rewritten = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION)
            rewritten.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_AND
            rewritten.binary_operation.left_operand = self._clone_expression_deep(
                left_operand.binary_operation.left_operand
            )
            rewritten.binary_operation.right_operand = rewritten_comparison
            return rewritten

        i = 0
        while i + 1 < len(block):
            declaration = block[i]
            next_statement = block[i + 1]

            if (
                declaration.type == AST_STATEMENT.AST_STATEMENT_GENERIC_FOR
                and len(declaration.assignment.expressions) > 1
            ):
                side_effect_count = 0
                while (
                    side_effect_count < len(declaration.assignment.expressions) - 1
                    and declaration.assignment.expressions[side_effect_count].type
                    == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                ):
                    side_effect_count += 1

                if side_effect_count:
                    extracted_expressions = declaration.assignment.expressions[:side_effect_count]
                    declaration.assignment.expressions = declaration.assignment.expressions[
                        side_effect_count:
                    ]
                    loop_label = declaration.instruction.label
                    declaration.instruction.label = INVALID_ID

                    for offset, expression in enumerate(extracted_expressions):
                        call_statement = self.new_statement(
                            AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL
                        )
                        call_statement.assignment.expressions = [expression]
                        call_statement.instruction.id = INVALID_ID
                        call_statement.instruction.target = INVALID_ID
                        call_statement.instruction.label = (
                            loop_label if offset == 0 else INVALID_ID
                        )
                        block.insert(i + offset, call_statement)

                    i += side_effect_count
                    continue

            if (
                declaration.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                and len(declaration.assignment.variables) == 1
                and len(declaration.assignment.expressions) == 1
                and declaration.assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and declaration.assignment.expressions[-1].type
                != AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                and (
                    (
                        next_statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                        and not function.is_valid_label(next_statement.instruction.label)
                    )
                    or (
                        next_statement.type == AST_STATEMENT.AST_STATEMENT_IF
                        and declaration.assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                        and declaration.assignment.expressions[-1].variable.type
                        == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                    )
                )
            ):
                slot = declaration.assignment.variables[-1].slot
                slot_scope = declaration.assignment.variables[-1].slot_scope
                used_later = False
                for offset in range(i + 2, len(block)):
                    if statement_slot_use_count(block[offset], slot, slot_scope):
                        used_later = True
                        break
                uses_in_next_statement = statement_slot_use_count(
                    next_statement, slot, slot_scope
                )
                if not used_later and uses_in_next_statement == 1:
                    rewritten_next_statement = clone_statement_preserving_scopes(
                        next_statement
                    )
                    replaced = self._replace_slot_in_statement(
                        rewritten_next_statement,
                        slot,
                        declaration.assignment.expressions[-1],
                        declaration.assignment.variables[-1].slot_scope,
                    )
                    if replaced == 1:
                        if (
                            function.is_valid_label(declaration.instruction.label)
                            and not function.is_valid_label(
                                rewritten_next_statement.instruction.label
                            )
                        ):
                            rewritten_next_statement.instruction.label = (
                                declaration.instruction.label
                            )
                        block[i + 1] = rewritten_next_statement
                        if declaration.assignment.variables[-1].slot_scope is not None:
                            function.slot_scope_collector.remove_scope(
                                declaration.assignment.variables[-1].slot,
                                declaration.assignment.variables[-1].slot_scope,
                            )
                        del block[i]
                        continue

            if (
                declaration.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                and next_statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                and len(declaration.assignment.variables) == 1
                and len(declaration.assignment.expressions) == 1
                and len(next_statement.assignment.variables) == 1
                and len(next_statement.assignment.expressions) == 1
                and declaration.assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and next_statement.assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and declaration.assignment.variables[-1].slot
                == next_statement.assignment.variables[-1].slot
                and next_statement.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                and next_statement.assignment.expressions[-1].binary_operation.type
                == AST_BINARY_OPERATION.AST_BINARY_OR
            ):
                left_operand = (
                    next_statement.assignment.expressions[-1].binary_operation.left_operand
                )
                if (
                    left_operand.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and left_operand.variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
                    and left_operand.variable.slot
                    == declaration.assignment.variables[-1].slot
                    and not function.is_valid_label(next_statement.instruction.label)
                ):
                    next_statement.assignment.expressions[-1].binary_operation.left_operand = (
                        declaration.assignment.expressions[-1]
                    )
                    declaration.assignment.expressions[-1] = (
                        next_statement.assignment.expressions[-1]
                    )
                    del block[i + 1]
                    continue

            if (
                declaration.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                and next_statement.type == AST_STATEMENT.AST_STATEMENT_RETURN
                and len(declaration.assignment.variables) == 1
                and len(declaration.assignment.expressions) == 1
                and len(next_statement.assignment.expressions) == 1
                and declaration.assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and next_statement.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                and next_statement.assignment.expressions[-1].variable.type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and declaration.assignment.variables[-1].slot
                == next_statement.assignment.expressions[-1].variable.slot
                and not function.is_valid_label(declaration.instruction.label)
            ):
                next_statement.assignment.expressions[-1] = declaration.assignment.expressions[-1]
                if declaration.assignment.variables[-1].slot_scope is not None:
                    function.slot_scope_collector.remove_scope(
                        declaration.assignment.variables[-1].slot,
                        declaration.assignment.variables[-1].slot_scope,
                    )
                del block[i]
                continue

            if (
                declaration.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                and next_statement.type == AST_STATEMENT.AST_STATEMENT_RETURN
                and len(declaration.assignment.variables) == 1
                and len(declaration.assignment.expressions) == 1
                and declaration.assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and len(next_statement.assignment.expressions) == 1
                and not function.is_valid_label(declaration.instruction.label)
            ):
                slot = declaration.assignment.variables[-1].slot
                rewritten_return_expression = self._clone_expression_deep(
                    next_statement.assignment.expressions[-1]
                )
                replaced = self._replace_slot_in_expression(
                    rewritten_return_expression,
                    slot,
                    declaration.assignment.expressions[-1],
                    declaration.assignment.variables[-1].slot_scope,
                )
                if replaced == 1:
                    next_statement.assignment.expressions[-1] = rewritten_return_expression
                    if declaration.assignment.variables[-1].slot_scope is not None:
                        function.slot_scope_collector.remove_scope(
                            declaration.assignment.variables[-1].slot,
                            declaration.assignment.variables[-1].slot_scope,
                        )
                    del block[i]
                    continue

            if (
                declaration.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                and next_statement.type == AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR
                and len(declaration.assignment.variables) == 1
                and len(declaration.assignment.expressions) == 1
                and declaration.assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and declaration.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                and declaration.assignment.expressions[-1].binary_operation.type
                == AST_BINARY_OPERATION.AST_BINARY_OR
                and len(next_statement.assignment.expressions) >= 1
                and next_statement.assignment.expressions[0].type
                == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                and next_statement.assignment.expressions[0].variable.type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and next_statement.assignment.expressions[0].variable.slot
                == declaration.assignment.variables[-1].slot
                and not function.is_valid_label(declaration.instruction.label)
                and not function.is_valid_label(next_statement.instruction.label)
            ):
                next_statement.assignment.expressions[0] = declaration.assignment.expressions[-1]
                if declaration.assignment.variables[-1].slot_scope is not None:
                    function.slot_scope_collector.remove_scope(
                        declaration.assignment.variables[-1].slot,
                        declaration.assignment.variables[-1].slot_scope,
                    )
                del block[i]
                continue

            if i + 2 < len(block):
                if_statement = block[i + 1]
                return_statement = block[i + 2]
                if (
                    declaration.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and if_statement.type == AST_STATEMENT.AST_STATEMENT_IF
                    and return_statement.type == AST_STATEMENT.AST_STATEMENT_RETURN
                    and len(declaration.assignment.variables) == 1
                    and declaration.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and len(return_statement.assignment.expressions) == 1
                    and return_statement.assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    and return_statement.assignment.expressions[-1].variable.type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and return_statement.assignment.expressions[-1].variable.slot
                    == declaration.assignment.variables[-1].slot
                    and len(if_statement.block) >= 2
                    and if_statement.block[0].type == AST_STATEMENT.AST_STATEMENT_IF
                    and if_statement.block[1].type == AST_STATEMENT.AST_STATEMENT_ELSE
                    and len(if_statement.block[0].assignment.expressions) == 1
                    and not function.is_valid_label(declaration.instruction.label)
                    and not function.is_valid_label(if_statement.instruction.label)
                ):
                    then_candidates = [
                        s
                        for s in if_statement.block[0].block
                        if s.type != AST_STATEMENT.AST_STATEMENT_EMPTY
                    ]
                    else_candidates = [
                        s
                        for s in if_statement.block[1].block
                        if s.type != AST_STATEMENT.AST_STATEMENT_EMPTY
                    ]
                    if (
                        len(then_candidates) == 1
                        and len(else_candidates) == 1
                        and then_candidates[0].type
                        == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                        and else_candidates[0].type
                        == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                        and len(then_candidates[0].assignment.variables) == 1
                        and len(else_candidates[0].assignment.variables) == 1
                        and then_candidates[0].assignment.variables[-1].type
                        == AST_VARIABLE.AST_VARIABLE_SLOT
                        and else_candidates[0].assignment.variables[-1].type
                        == AST_VARIABLE.AST_VARIABLE_SLOT
                        and then_candidates[0].assignment.variables[-1].slot
                        == declaration.assignment.variables[-1].slot
                        and else_candidates[0].assignment.variables[-1].slot
                        == declaration.assignment.variables[-1].slot
                        and len(then_candidates[0].assignment.expressions) == 1
                        and len(else_candidates[0].assignment.expressions) == 1
                    ):
                        then_bool = self._bool_constant_value(
                            then_candidates[0].assignment.expressions[-1]
                        )
                        else_bool = self._bool_constant_value(
                            else_candidates[0].assignment.expressions[-1]
                        )
                        if then_bool is not None and else_bool is not None and then_bool != else_bool:
                            condition_expression = self._clone_expression_deep(
                                if_statement.block[0].assignment.expressions[-1]
                            )
                            if then_bool:
                                replacement = condition_expression
                            else:
                                replacement = self._negate_condition_expression(
                                    condition_expression
                                )
                            return_statement.assignment.expressions[-1] = (
                                self._simplify_safe_double_not_expression(replacement)
                            )
                            del block[i : i + 2]
                            continue

            if (
                declaration.type
                in (
                    AST_STATEMENT.AST_STATEMENT_DECLARATION,
                    AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                )
                and len(declaration.assignment.variables) == 1
                and len(declaration.assignment.expressions) == 1
                and declaration.assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                if_else_pair = get_if_else_pair(i + 1)
                if if_else_pair is not None:
                    if_statement_node, else_statement_node, uses_adjacent_else = if_else_pair
                    if len(if_statement_node.assignment.expressions) == 1:
                        then_assignment = get_single_assignment_from_branch(if_statement_node)
                        else_assignment = get_single_assignment_from_branch(else_statement_node)
                        if (
                            then_assignment is not None
                            and else_assignment is not None
                            and then_assignment.assignment.variables[-1].slot
                            == declaration.assignment.variables[-1].slot
                            and else_assignment.assignment.variables[-1].slot
                            == declaration.assignment.variables[-1].slot
                        ):
                            then_bool = self._bool_constant_value(
                                then_assignment.assignment.expressions[-1]
                            )
                            else_bool = self._bool_constant_value(
                                else_assignment.assignment.expressions[-1]
                            )
                            if (
                                then_bool is not None
                                and else_bool is not None
                                and then_bool != else_bool
                            ):
                                slot = declaration.assignment.variables[-1].slot
                                slot_scope = declaration.assignment.variables[-1].slot_scope
                                rewritten_condition = self._clone_expression_deep(
                                    if_statement_node.assignment.expressions[-1]
                                )
                                replaced = self._replace_slot_in_expression(
                                    rewritten_condition,
                                    slot,
                                    declaration.assignment.expressions[-1],
                                    slot_scope,
                                )
                                if replaced == 1:
                                    if then_bool:
                                        merged_expression = rewritten_condition
                                    else:
                                        merged_expression = self._negate_condition_expression(
                                            rewritten_condition
                                        )
                                    declaration.assignment.expressions[-1] = (
                                        self._simplify_safe_double_not_expression(
                                            merged_expression
                                        )
                                    )
                                    declaration.assignment.expressions[-1] = (
                                        rewrite_and_comparison_expression(
                                            declaration.assignment.expressions[-1]
                                        )
                                    )
                                    if uses_adjacent_else:
                                        del block[i + 1 : i + 3]
                                    else:
                                        del block[i + 1]
                                    continue

            if (
                declaration.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                and len(declaration.assignment.variables) == 1
                and declaration.assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                and (
                    not declaration.assignment.expressions
                    or (
                        len(declaration.assignment.expressions) == 1
                        and declaration.assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                        and declaration.assignment.expressions[-1].constant.type
                        == AST_CONSTANT.AST_CONSTANT_NIL
                    )
                )
            ):
                if_else_pair = get_if_else_pair(i + 1)
                if if_else_pair is not None:
                    if_statement_node, else_statement_node, uses_adjacent_else = if_else_pair
                    if len(if_statement_node.assignment.expressions) == 1:
                        then_assignment = get_single_assignment_from_branch(if_statement_node)
                        else_assignment = get_single_assignment_from_branch(else_statement_node)
                        if (
                            then_assignment is not None
                            and else_assignment is not None
                            and then_assignment.assignment.variables[-1].slot
                            == declaration.assignment.variables[-1].slot
                            and else_assignment.assignment.variables[-1].slot
                            == declaration.assignment.variables[-1].slot
                            and then_assignment.assignment.expressions[-1].type
                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            and then_assignment.assignment.expressions[-1].constant.type
                            not in (
                                AST_CONSTANT.AST_CONSTANT_FALSE,
                                AST_CONSTANT.AST_CONSTANT_NIL,
                            )
                        ):
                            ternary_expr = self.new_expression(
                                AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                            )
                            ternary_expr.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_OR
                            and_expr = self.new_expression(
                                AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                            )
                            and_expr.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_AND
                            and_expr.binary_operation.left_operand = self._clone_expression_deep(
                                if_statement_node.assignment.expressions[-1]
                            )
                            and_expr.binary_operation.right_operand = self._clone_expression_deep(
                                then_assignment.assignment.expressions[-1]
                            )
                            ternary_expr.binary_operation.left_operand = and_expr
                            ternary_expr.binary_operation.right_operand = self._clone_expression_deep(
                                else_assignment.assignment.expressions[-1]
                            )
                            declaration.assignment.expressions = [ternary_expr]
                            if uses_adjacent_else:
                                del block[i + 1 : i + 3]
                            else:
                                del block[i + 1]
                            continue

            declaration_a = block[i]
            non_empty_two: list[int] = []
            scan_two = i + 1
            while scan_two < len(block) and len(non_empty_two) < 2:
                if block[scan_two].type != AST_STATEMENT.AST_STATEMENT_EMPTY:
                    non_empty_two.append(scan_two)
                scan_two += 1

            if len(non_empty_two) == 2:
                b2_index, c2_index = non_empty_two
                declaration_b2 = block[b2_index]
                declaration_c2 = block[c2_index]
                between_only_empty_2 = True
                for check_index in range(i + 1, c2_index):
                    if check_index == b2_index:
                        continue
                    if block[check_index].type != AST_STATEMENT.AST_STATEMENT_EMPTY:
                        between_only_empty_2 = False
                        break

                if (
                    declaration_a.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and declaration_b2.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and declaration_c2.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and between_only_empty_2
                    and len(declaration_a.assignment.variables) == 1
                    and len(declaration_b2.assignment.variables) == 1
                    and len(declaration_c2.assignment.variables) == 1
                    and len(declaration_a.assignment.expressions) == 1
                    and len(declaration_b2.assignment.expressions) == 1
                    and len(declaration_c2.assignment.expressions) == 1
                    and declaration_a.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and declaration_b2.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and declaration_c2.assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                    and is_pure_expression(declaration_a.assignment.expressions[-1])
                    and is_pure_expression(declaration_b2.assignment.expressions[-1])
                ):
                    assert_call = declaration_c2.assignment.expressions[-1].function_call
                    if (
                        assert_call.function is not None
                        and assert_call.function.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                        and assert_call.function.variable.type == AST_VARIABLE.AST_VARIABLE_GLOBAL
                        and assert_call.function.variable.name == "assert"
                        and len(assert_call.arguments) == 1
                        and assert_call.arguments[0].type
                        == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                    ):
                        open_call = assert_call.arguments[0].function_call
                        if (
                            open_call.function is not None
                            and open_call.function.type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and open_call.function.variable.type
                            == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                            and open_call.function.variable.table is not None
                            and open_call.function.variable.table.type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and open_call.function.variable.table.variable.type
                            == AST_VARIABLE.AST_VARIABLE_GLOBAL
                            and open_call.function.variable.table.variable.name == "io"
                            and open_call.function.variable.table_index is not None
                            and open_call.function.variable.table_index.type
                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            and open_call.function.variable.table_index.constant.type
                            == AST_CONSTANT.AST_CONSTANT_STRING
                            and open_call.function.variable.table_index.constant.string
                            == "open"
                            and len(open_call.arguments) >= 1
                        ):
                            slot_a = declaration_a.assignment.variables[-1].slot
                            slot_b = declaration_b2.assignment.variables[-1].slot
                            scope_a = declaration_a.assignment.variables[-1].slot_scope
                            scope_b = declaration_b2.assignment.variables[-1].slot_scope
                            path_expression = self._clone_expression_deep(
                                open_call.arguments[0]
                            )

                            replaced_a = self._replace_slot_in_expression(
                                path_expression,
                                slot_a,
                                declaration_a.assignment.expressions[-1],
                                scope_a,
                            )
                            if replaced_a == 0 and scope_a is not None:
                                replaced_a = self._replace_slot_in_expression(
                                    path_expression,
                                    slot_a,
                                    declaration_a.assignment.expressions[-1],
                                    None,
                                )
                            replaced_b = self._replace_slot_in_expression(
                                path_expression,
                                slot_b,
                                declaration_b2.assignment.expressions[-1],
                                scope_b,
                            )
                            if replaced_b == 0 and scope_b is not None:
                                replaced_b = self._replace_slot_in_expression(
                                    path_expression,
                                    slot_b,
                                    declaration_b2.assignment.expressions[-1],
                                    None,
                                )
                            if replaced_a == 1 and replaced_b == 1:
                                declaration_a.assignment.expressions[-1] = path_expression
                                path_variable_expression = self.new_expression(
                                    AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                )
                                path_variable_expression.variable = self._clone_variable(
                                    declaration_a.assignment.variables[-1]
                                )
                                open_call.arguments[0] = path_variable_expression

                                if declaration_b2.assignment.variables[-1].slot_scope is not None:
                                    function.slot_scope_collector.remove_scope(
                                        declaration_b2.assignment.variables[-1].slot,
                                        declaration_b2.assignment.variables[-1].slot_scope,
                                    )
                                del block[b2_index]
                                continue

            declaration_b: Optional[Statement] = None
            declaration_c: Optional[Statement] = None
            declaration_d: Optional[Statement] = None
            between_only_empty = False
            b_index = c_index = d_index = INVALID_ID
            non_empty_indices: list[int] = []
            scan_index = i + 1
            while scan_index < len(block) and len(non_empty_indices) < 3:
                if block[scan_index].type != AST_STATEMENT.AST_STATEMENT_EMPTY:
                    non_empty_indices.append(scan_index)
                scan_index += 1

            if len(non_empty_indices) == 3:
                b_index, c_index, d_index = non_empty_indices
                declaration_b = block[b_index]
                declaration_c = block[c_index]
                declaration_d = block[d_index]
                between_only_empty = True
                for check_index in range(i + 1, d_index):
                    if check_index in (b_index, c_index):
                        continue
                    if block[check_index].type != AST_STATEMENT.AST_STATEMENT_EMPTY:
                        between_only_empty = False
                        break

            if (
                    declaration_a.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and declaration_b is not None
                    and declaration_c is not None
                    and declaration_d is not None
                    and declaration_b.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and declaration_c.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and declaration_d.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and between_only_empty
                    and len(declaration_a.assignment.variables) == 1
                    and len(declaration_b.assignment.variables) == 1
                    and len(declaration_c.assignment.variables) == 1
                    and len(declaration_d.assignment.variables) == 1
                    and len(declaration_a.assignment.expressions) == 1
                    and len(declaration_b.assignment.expressions) == 1
                    and len(declaration_c.assignment.expressions) == 1
                    and len(declaration_d.assignment.expressions) == 1
                    and declaration_a.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and declaration_b.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and declaration_c.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and declaration_d.assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                    and is_pure_expression(declaration_a.assignment.expressions[-1])
                    and is_pure_expression(declaration_b.assignment.expressions[-1])
                    and is_pure_expression(declaration_c.assignment.expressions[-1])
                ):
                    assert_call = declaration_d.assignment.expressions[-1].function_call
                    if (
                        assert_call.function is not None
                        and assert_call.function.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                        and assert_call.function.variable.type == AST_VARIABLE.AST_VARIABLE_GLOBAL
                        and assert_call.function.variable.name == "assert"
                        and len(assert_call.arguments) == 1
                        and assert_call.arguments[0].type
                        == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                    ):
                        open_call = assert_call.arguments[0].function_call
                        if (
                            open_call.function is not None
                            and open_call.function.type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and open_call.function.variable.type
                            == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                            and open_call.function.variable.table is not None
                            and open_call.function.variable.table.type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and open_call.function.variable.table.variable.type
                            == AST_VARIABLE.AST_VARIABLE_GLOBAL
                            and open_call.function.variable.table.variable.name == "io"
                            and open_call.function.variable.table_index is not None
                            and open_call.function.variable.table_index.type
                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            and open_call.function.variable.table_index.constant.type
                            == AST_CONSTANT.AST_CONSTANT_STRING
                            and open_call.function.variable.table_index.constant.string
                            == "open"
                            and len(open_call.arguments) >= 1
                        ):
                            slot_a = declaration_a.assignment.variables[-1].slot
                            slot_b = declaration_b.assignment.variables[-1].slot
                            slot_c = declaration_c.assignment.variables[-1].slot
                            scope_a = declaration_a.assignment.variables[-1].slot_scope
                            scope_b = declaration_b.assignment.variables[-1].slot_scope
                            scope_c = declaration_c.assignment.variables[-1].slot_scope
                            path_expression = self._clone_expression_deep(
                                open_call.arguments[0]
                            )

                            replaced_a = self._replace_slot_in_expression(
                                path_expression,
                                slot_a,
                                declaration_a.assignment.expressions[-1],
                                scope_a,
                            )
                            if replaced_a == 0 and scope_a is not None:
                                replaced_a = self._replace_slot_in_expression(
                                    path_expression,
                                    slot_a,
                                    declaration_a.assignment.expressions[-1],
                                    None,
                                )
                            replaced_b = self._replace_slot_in_expression(
                                path_expression,
                                slot_b,
                                declaration_b.assignment.expressions[-1],
                                scope_b,
                            )
                            if replaced_b == 0 and scope_b is not None:
                                replaced_b = self._replace_slot_in_expression(
                                    path_expression,
                                    slot_b,
                                    declaration_b.assignment.expressions[-1],
                                    None,
                                )
                            replaced_c = self._replace_slot_in_expression(
                                path_expression,
                                slot_c,
                                declaration_c.assignment.expressions[-1],
                                scope_c,
                            )
                            if replaced_c == 0 and scope_c is not None:
                                replaced_c = self._replace_slot_in_expression(
                                    path_expression,
                                    slot_c,
                                    declaration_c.assignment.expressions[-1],
                                    None,
                                )
                            if replaced_a == 1 and replaced_b == 1 and replaced_c == 1:
                                declaration_a.assignment.expressions[-1] = path_expression
                                path_variable_expression = self.new_expression(
                                    AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                )
                                path_variable_expression.variable = self._clone_variable(
                                    declaration_a.assignment.variables[-1]
                                )
                                open_call.arguments[0] = path_variable_expression

                                if declaration_b.assignment.variables[-1].slot_scope is not None:
                                    function.slot_scope_collector.remove_scope(
                                        declaration_b.assignment.variables[-1].slot,
                                        declaration_b.assignment.variables[-1].slot_scope,
                                    )
                                if declaration_c.assignment.variables[-1].slot_scope is not None:
                                    function.slot_scope_collector.remove_scope(
                                        declaration_c.assignment.variables[-1].slot,
                                        declaration_c.assignment.variables[-1].slot_scope,
                                    )

                                del block[c_index]
                                del block[b_index]
                                continue

            if (
                declaration.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                and len(declaration.assignment.variables) == 1
                and len(declaration.assignment.expressions) == 1
                and declaration.assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and is_pure_expression(declaration.assignment.expressions[-1])
                and not function.is_valid_label(declaration.instruction.label)
            ):
                slot = declaration.assignment.variables[-1].slot
                slot_scope = declaration.assignment.variables[-1].slot_scope
                inline_applied = False

                for target_index in range(i + 1, min(len(block), i + 6)):
                    target_statement = block[target_index]
                    if function.is_valid_label(target_statement.instruction.label):
                        break
                    if (
                        target_statement.type
                        != AST_STATEMENT.AST_STATEMENT_DECLARATION
                        or len(target_statement.assignment.variables) != 1
                        or len(target_statement.assignment.expressions) != 1
                        or target_statement.assignment.expressions[-1].type
                        != AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                    ):
                        continue

                    can_cross = True
                    for middle_index in range(i + 1, target_index):
                        middle_statement = block[middle_index]
                        if (
                            function.is_valid_label(middle_statement.instruction.label)
                            or statement_slot_use_count(
                                middle_statement, slot, slot_scope
                            )
                            or middle_statement.type
                            != AST_STATEMENT.AST_STATEMENT_DECLARATION
                            or len(middle_statement.assignment.variables) != 1
                            or len(middle_statement.assignment.expressions) != 1
                            or not is_pure_expression(
                                middle_statement.assignment.expressions[-1]
                            )
                        ):
                            can_cross = False
                            break

                    if not can_cross:
                        break

                    uses_in_target = statement_slot_use_count(
                        target_statement, slot, slot_scope
                    )
                    replacement_scope = slot_scope
                    if uses_in_target == 0 and slot_scope is not None:
                        uses_in_target = statement_slot_use_count(target_statement, slot, None)
                        replacement_scope = None
                    if uses_in_target != 1:
                        continue

                    rewritten_target = clone_statement_preserving_scopes(target_statement)
                    replaced = self._replace_slot_in_statement(
                        rewritten_target,
                        slot,
                        declaration.assignment.expressions[-1],
                        replacement_scope,
                    )
                    if replaced != 1:
                        continue

                    block[target_index] = rewritten_target
                    if declaration.assignment.variables[-1].slot_scope is not None:
                        function.slot_scope_collector.remove_scope(
                            declaration.assignment.variables[-1].slot,
                            declaration.assignment.variables[-1].slot_scope,
                        )
                    del block[i]
                    inline_applied = True
                    break

                if inline_applied:
                    continue

            i += 1

        self._simplify_safe_double_not_block(block)

    def _compatibility_folds(self, function: Function, block: list[Statement]) -> None:
        for statement in block:
            if statement.block:
                self._compatibility_folds(function, statement.block)

        self._compatibility_merge_table_constructor_fields(function, block)
        self._compatibility_inline_if_temp_conditions(function, block)
        self._merge_nested_if_conditions(block)

    def _compatibility_merge_table_constructor_fields(
        self, function: Function, block: list[Statement]
    ) -> None:
        def has_self_reference(target_slot: int, expression: Optional[Expression]) -> bool:
            if expression is None:
                return False
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
                variable = expression.variable
                if variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    return variable.slot == target_slot
                if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    return has_self_reference(target_slot, variable.table) or has_self_reference(
                        target_slot, variable.table_index
                    )
                return False
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
                function_call = expression.function_call
                if has_self_reference(target_slot, function_call.function):
                    return True
                if has_self_reference(target_slot, function_call.multres_argument):
                    return True
                for argument in function_call.arguments:
                    if has_self_reference(target_slot, argument):
                        return True
                return False
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
                for field in expression.table.fields:
                    if has_self_reference(target_slot, field.key) or has_self_reference(
                        target_slot, field.value
                    ):
                        return True
                return has_self_reference(target_slot, expression.table.multres_field)
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
                return has_self_reference(
                    target_slot, expression.binary_operation.left_operand
                ) or has_self_reference(target_slot, expression.binary_operation.right_operand)
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
                return has_self_reference(target_slot, expression.unary_operation.operand)
            return False

        i = 0
        while i < len(block):
            base = block[i]
            if (
                base.type not in (
                    AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                    AST_STATEMENT.AST_STATEMENT_DECLARATION,
                )
                or len(base.assignment.variables) != 1
                or len(base.assignment.expressions) != 1
                or base.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
                or base.assignment.expressions[-1].type != AST_EXPRESSION.AST_EXPRESSION_TABLE
                or base.assignment.expressions[-1].table.multres_field is not None
            ):
                i += 1
                continue

            slot = base.assignment.variables[-1].slot
            table_expression = base.assignment.expressions[-1]
            merged_any = False
            j = i + 1

            while j < len(block):
                candidate = block[j]
                if candidate.type == AST_STATEMENT.AST_STATEMENT_EMPTY and not function.is_valid_label(
                    candidate.instruction.label
                ):
                    j += 1
                    continue

                if (
                    candidate.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    or len(candidate.assignment.variables) != 1
                    or len(candidate.assignment.expressions) != 1
                    or candidate.assignment.variables[-1].type
                    != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                    or candidate.assignment.variables[-1].table is None
                    or candidate.assignment.variables[-1].table.type
                    != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                    or candidate.assignment.variables[-1].table.variable.type
                    != AST_VARIABLE.AST_VARIABLE_SLOT
                    or candidate.assignment.variables[-1].table.variable.slot != slot
                    or function.is_valid_label(candidate.instruction.label)
                ):
                    break

                table_variable = candidate.assignment.variables[-1]
                value_expression = candidate.assignment.expressions[-1]
                if (
                    not table_variable.is_multres
                    and Ast.get_constant_type(table_variable.table_index)
                    > CONSTANT_TYPE.NIL_CONSTANT
                    and Ast.get_constant_type(value_expression)
                    != CONSTANT_TYPE.INVALID_CONSTANT
                ):
                    break
                if (
                    not table_variable.is_multres
                    and has_self_reference(slot, table_variable.table_index)
                ):
                    break
                if has_self_reference(slot, value_expression):
                    break

                if table_variable.is_multres:
                    table_expression.table.multres_index = table_variable.multres_index
                    table_expression.table.multres_field = value_expression
                else:
                    if (
                        table_variable.table_index is not None
                        and table_variable.table_index.type
                        == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                        and table_variable.table_index.constant.type
                        == AST_CONSTANT.AST_CONSTANT_STRING
                    ):
                        for k in range(
                            len(table_expression.table.constants.fields) - 1, -1, -1
                        ):
                            key = table_expression.table.constants.fields[k].key
                            value = table_expression.table.constants.fields[k].value
                            if (
                                key is None
                                or key.type != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                or key.constant.type != AST_CONSTANT.AST_CONSTANT_STRING
                                or key.constant.string
                                != table_variable.table_index.constant.string
                            ):
                                continue
                            if (
                                value is not None
                                and value.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                and value.constant.type == AST_CONSTANT.AST_CONSTANT_NIL
                            ):
                                del table_expression.table.constants.fields[k]
                            break

                    table_expression.table.fields.append(
                        AstTableField(
                            key=table_variable.table_index,
                            value=value_expression,
                        )
                    )

                del block[j]
                merged_any = True
                continue

            if merged_any:
                continue
            i += 1

    def _compatibility_inline_if_temp_conditions(
        self, function: Function, block: list[Statement]
    ) -> None:
        def expression_slot_use_count(
            expression: Optional[Expression],
            slot: int,
            target_scope: Optional[ScopeCell],
        ) -> int:
            if expression is None:
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
                variable = expression.variable
                if variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    if variable.slot != slot:
                        return 0
                    if target_scope is None:
                        return 1
                    return 1 if variable.slot_scope is target_scope else 0
                if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    return expression_slot_use_count(
                        variable.table, slot, target_scope
                    ) + expression_slot_use_count(variable.table_index, slot, target_scope)
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
                function_call = expression.function_call
                uses = expression_slot_use_count(function_call.function, slot, target_scope)
                uses += expression_slot_use_count(
                    function_call.multres_argument, slot, target_scope
                )
                for argument in function_call.arguments:
                    uses += expression_slot_use_count(argument, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
                table = expression.table
                uses = expression_slot_use_count(table.multres_field, slot, target_scope)
                for field in table.fields:
                    uses += expression_slot_use_count(field.key, slot, target_scope)
                    uses += expression_slot_use_count(field.value, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
                return expression_slot_use_count(
                    expression.binary_operation.left_operand, slot, target_scope
                ) + expression_slot_use_count(
                    expression.binary_operation.right_operand, slot, target_scope
                )
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
                return expression_slot_use_count(
                    expression.unary_operation.operand, slot, target_scope
                )
            return 0

        def statement_slot_use_count(
            statement: Statement, slot: int, target_scope: Optional[ScopeCell]
        ) -> int:
            uses = expression_slot_use_count(
                statement.assignment.multres_return, slot, target_scope
            )
            for expression in statement.assignment.expressions:
                uses += expression_slot_use_count(expression, slot, target_scope)
            for variable in statement.assignment.variables:
                if variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    continue
                uses += expression_slot_use_count(variable.table, slot, target_scope)
                uses += expression_slot_use_count(variable.table_index, slot, target_scope)
            for nested_statement in statement.block:
                uses += statement_slot_use_count(nested_statement, slot, target_scope)
            return uses

        i = 0
        while i < len(block):
            statement = block[i]
            if (
                statement.type != AST_STATEMENT.AST_STATEMENT_IF
                or len(statement.assignment.expressions) != 1
            ):
                i += 1
                continue

            non_empty_children: list[tuple[int, Statement]] = [
                (idx, child)
                for idx, child in enumerate(statement.block)
                if child.type != AST_STATEMENT.AST_STATEMENT_EMPTY
            ]
            if len(non_empty_children) != 2:
                i += 1
                continue

            declaration_index, declaration = non_empty_children[0]
            inner_if_index, inner_if = non_empty_children[1]
            if (
                declaration.type != AST_STATEMENT.AST_STATEMENT_DECLARATION
                or inner_if.type != AST_STATEMENT.AST_STATEMENT_IF
                or len(declaration.assignment.variables) != 1
                or len(declaration.assignment.expressions) != 1
                or declaration.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
                or len(inner_if.assignment.expressions) != 1
            ):
                i += 1
                continue

            if (
                declaration.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION
                and declaration.assignment.expressions[-1].unary_operation.type
                == AST_UNARY_OPERATION.AST_UNARY_LENGTH
                and inner_if.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                and inner_if.assignment.expressions[-1].binary_operation.type
                in (
                    AST_BINARY_OPERATION.AST_BINARY_AND,
                    AST_BINARY_OPERATION.AST_BINARY_OR,
                )
            ):
                i += 1
                continue

            slot = declaration.assignment.variables[-1].slot
            slot_scope = declaration.assignment.variables[-1].slot_scope
            uses_in_inner_condition = expression_slot_use_count(
                inner_if.assignment.expressions[-1], slot, slot_scope
            )
            if uses_in_inner_condition != 1:
                i += 1
                continue

            uses_in_inner_body = 0
            for child in inner_if.block:
                uses_in_inner_body += statement_slot_use_count(child, slot, slot_scope)
            if uses_in_inner_body != 0:
                i += 1
                continue

            rewritten_condition = self._clone_expression_deep(inner_if.assignment.expressions[-1])
            replaced = self._replace_slot_in_expression(
                rewritten_condition,
                slot,
                declaration.assignment.expressions[-1],
                slot_scope,
            )
            if replaced != 1:
                i += 1
                continue

            inner_if.assignment.expressions[-1] = rewritten_condition
            if (
                function.is_valid_label(declaration.instruction.label)
                and not function.is_valid_label(inner_if.instruction.label)
            ):
                inner_if.instruction.label = declaration.instruction.label
            if declaration.assignment.variables[-1].slot_scope is not None:
                function.slot_scope_collector.remove_scope(
                    declaration.assignment.variables[-1].slot,
                    declaration.assignment.variables[-1].slot_scope,
                )
            del statement.block[declaration_index]

            if inner_if_index > declaration_index:
                inner_if_index -= 1
            statement.block[inner_if_index] = inner_if
            continue

    @staticmethod
    def _is_comparison_expression(expression: Optional[Expression]) -> bool:
        return (
            expression is not None
            and expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
            and expression.binary_operation.type
            in (
                AST_BINARY_OPERATION.AST_BINARY_LESS_THAN,
                AST_BINARY_OPERATION.AST_BINARY_LESS_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_GREATER_THEN,
                AST_BINARY_OPERATION.AST_BINARY_GREATER_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_NOT_EQUAL,
            )
        )

    def _simplify_safe_double_not_expression(
        self, expression: Optional[Expression]
    ) -> Optional[Expression]:
        if expression is None:
            return None
        if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            expression.binary_operation.left_operand = self._simplify_safe_double_not_expression(
                expression.binary_operation.left_operand
            )
            expression.binary_operation.right_operand = self._simplify_safe_double_not_expression(
                expression.binary_operation.right_operand
            )
            return expression
        if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            expression.unary_operation.operand = self._simplify_safe_double_not_expression(
                expression.unary_operation.operand
            )
            if (
                expression.unary_operation.type == AST_UNARY_OPERATION.AST_UNARY_NOT
                and expression.unary_operation.operand is not None
                and expression.unary_operation.operand.type
                == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION
                and expression.unary_operation.operand.unary_operation.type
                == AST_UNARY_OPERATION.AST_UNARY_NOT
                and Ast._is_comparison_expression(
                    expression.unary_operation.operand.unary_operation.operand
                )
            ):
                return expression.unary_operation.operand.unary_operation.operand
            return expression
        return expression

    def _simplify_safe_double_not_block(self, block: list[Statement]) -> None:
        for statement in block:
            if statement.block:
                self._simplify_safe_double_not_block(statement.block)
            for index in range(len(statement.assignment.expressions)):
                statement.assignment.expressions[index] = self._simplify_safe_double_not_expression(
                    statement.assignment.expressions[index]
                )

    def _inline_short_lived_assignments(self, function: Function, block: list[Statement]) -> None:
        def should_skip_len_condition_inline(
            prev_statement: Statement, curr_statement: Statement
        ) -> bool:
            if (
                curr_statement.type != AST_STATEMENT.AST_STATEMENT_CONDITION
                or len(prev_statement.assignment.expressions) != 1
                or prev_statement.assignment.expressions[-1].type
                != AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION
                or prev_statement.assignment.expressions[-1].unary_operation.type
                != AST_UNARY_OPERATION.AST_UNARY_LENGTH
            ):
                return False
            target_index = Ast.get_block_index_from_id(
                block, curr_statement.instruction.target
            )
            return (
                target_index != INVALID_ID
                and 0 <= target_index < len(block)
                and block[target_index].type == AST_STATEMENT.AST_STATEMENT_EMPTY
            )

        for statement in block:
            if statement.block:
                self._inline_short_lived_assignments(function, statement.block)

        allowed_expression_types = {
            AST_EXPRESSION.AST_EXPRESSION_CONSTANT,
            AST_EXPRESSION.AST_EXPRESSION_VARIABLE,
            AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION,
            AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION,
        }

        i = 1
        while i < len(block):
            prev = block[i - 1]
            curr = block[i]
            if (
                curr.type == AST_STATEMENT.AST_STATEMENT_RETURN
                and len(curr.assignment.expressions) == 1
                and curr.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                and curr.assignment.expressions[-1].variable.type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and not function.is_valid_label(prev.instruction.label)
            ):
                return_var = curr.assignment.expressions[-1].variable

                # Pattern: local x; x = expr; return x  ->  return expr
                if (
                    i >= 2
                    and block[i - 2].type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and len(block[i - 2].assignment.variables) == 1
                    and block[i - 2].assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and (
                        not block[i - 2].assignment.expressions
                        or (
                            len(block[i - 2].assignment.expressions) == 1
                            and block[i - 2].assignment.expressions[-1].type
                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            and block[i - 2].assignment.expressions[-1].constant.type
                            == AST_CONSTANT.AST_CONSTANT_NIL
                        )
                    )
                    and prev.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(prev.assignment.variables) == 1
                    and prev.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and len(prev.assignment.expressions) == 1
                    and self._is_single_value_return_safe_expression(
                        prev.assignment.expressions[-1]
                    )
                    and not function.is_valid_label(prev.instruction.label)
                    and return_var.slot == prev.assignment.variables[-1].slot
                    and return_var.slot == block[i - 2].assignment.variables[-1].slot
                ):
                    curr.assignment.expressions[-1] = self._clone_expression_deep(
                        prev.assignment.expressions[-1]
                    )
                    declaration_var = block[i - 2].assignment.variables[-1]
                    if declaration_var.slot_scope is not None:
                        function.slot_scope_collector.remove_scope(
                            declaration_var.slot,
                            declaration_var.slot_scope,
                        )
                    if (
                        function.is_valid_label(block[i - 2].instruction.label)
                        and not function.is_valid_label(curr.instruction.label)
                    ):
                        curr.instruction.label = block[i - 2].instruction.label
                    del block[i - 2 : i]
                    i -= 1
                    continue

                # Pattern: x = expr; return x  or local x = expr; return x
                if (
                    prev.type
                    in (
                        AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                        AST_STATEMENT.AST_STATEMENT_DECLARATION,
                    )
                    and len(prev.assignment.variables) == 1
                    and prev.assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                    and len(prev.assignment.expressions) == 1
                    and self._is_single_value_return_safe_expression(
                        prev.assignment.expressions[-1]
                    )
                    and return_var.slot == prev.assignment.variables[-1].slot
                ):
                    curr.assignment.expressions[-1] = self._clone_expression_deep(
                        prev.assignment.expressions[-1]
                    )
                    if prev.assignment.variables[-1].slot_scope is not None:
                        function.slot_scope_collector.remove_scope(
                            prev.assignment.variables[-1].slot,
                            prev.assignment.variables[-1].slot_scope,
                        )
                    del block[i - 1]
                    i -= 1
                    continue

            if (
                prev.type
                in (
                    AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                    AST_STATEMENT.AST_STATEMENT_DECLARATION,
                )
                and len(prev.assignment.variables) == 1
                and prev.assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                and prev.assignment.variables[-1].slot_scope is not None
                and prev.assignment.variables[-1].slot_scope.scope.usages == 1
                and len(prev.assignment.expressions) == 1
                and prev.assignment.expressions[-1].type in allowed_expression_types
                and curr.instruction.id != INVALID_ID
                and not prev.assignment.forward_declaration
                and not function.is_valid_label(prev.instruction.label)
                and not function.is_valid_label(curr.instruction.label)
                and curr.type
                not in (
                    AST_STATEMENT.AST_STATEMENT_IF,
                )
                and not should_skip_len_condition_inline(prev, curr)
            ):
                slot = prev.assignment.variables[-1].slot
                replacement = prev.assignment.expressions[-1]
                replaced = self._replace_slot_in_statement(
                    curr,
                    slot,
                    replacement,
                    prev.assignment.variables[-1].slot_scope,
                )
                if replaced:
                    function.slot_scope_collector.remove_scope(
                        prev.assignment.variables[-1].slot,
                        prev.assignment.variables[-1].slot_scope,
                    )
                    del block[i - 1]
                    i -= 1
                    continue
            i += 1

    def _simplify_bool_return_constructs(self, block: list[Statement]) -> None:
        for statement in block:
            if statement.block:
                self._simplify_bool_return_constructs(statement.block)

        i = 0
        while i < len(block):
            statement = block[i]
            if statement.type != AST_STATEMENT.AST_STATEMENT_IF or len(statement.block) < 3:
                i += 1
                continue

            if_stmt = statement.block[0]
            else_stmt = statement.block[1]
            ret_stmt = statement.block[2]
            if (
                if_stmt.type != AST_STATEMENT.AST_STATEMENT_IF
                or else_stmt.type != AST_STATEMENT.AST_STATEMENT_ELSE
                or ret_stmt.type != AST_STATEMENT.AST_STATEMENT_RETURN
                or len(if_stmt.assignment.expressions) != 1
                or len(ret_stmt.assignment.expressions) != 1
            ):
                i += 1
                continue

            then_candidates = [
                s for s in if_stmt.block if s.type != AST_STATEMENT.AST_STATEMENT_EMPTY
            ]
            else_candidates = [
                s for s in else_stmt.block if s.type != AST_STATEMENT.AST_STATEMENT_EMPTY
            ]
            if len(then_candidates) != 1 or len(else_candidates) != 1:
                i += 1
                continue

            then_assign = then_candidates[0]
            else_assign = else_candidates[0]
            if (
                then_assign.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or else_assign.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or len(then_assign.assignment.variables) != 1
                or len(else_assign.assignment.variables) != 1
                or then_assign.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
                or else_assign.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
                or len(then_assign.assignment.expressions) != 1
                or len(else_assign.assignment.expressions) != 1
            ):
                i += 1
                continue

            ret_expression = ret_stmt.assignment.expressions[-1]
            if (
                ret_expression.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                or ret_expression.variable.type != AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                i += 1
                continue

            then_slot = then_assign.assignment.variables[-1]
            else_slot = else_assign.assignment.variables[-1]
            if (
                then_slot.slot != else_slot.slot
                or ret_expression.variable.slot != then_slot.slot
                or ret_expression.variable.slot_scope is not then_slot.slot_scope
                or ret_expression.variable.slot_scope is not else_slot.slot_scope
            ):
                i += 1
                continue

            then_bool = self._bool_constant_value(then_assign.assignment.expressions[-1])
            else_bool = self._bool_constant_value(else_assign.assignment.expressions[-1])
            if then_bool is None or else_bool is None or then_bool == else_bool:
                i += 1
                continue

            condition_expression = if_stmt.assignment.expressions[-1]
            if then_bool and not else_bool:
                replacement = self._clone_expression_deep(condition_expression)
            else:
                replacement = self._negate_condition_expression(condition_expression)
            ret_stmt.assignment.expressions[-1] = replacement
            del statement.block[0:2]
            i += 1

    def _merge_nested_if_conditions(self, block: list[Statement]) -> None:
        for statement in block:
            if statement.block:
                self._merge_nested_if_conditions(statement.block)

        i = 0
        while i < len(block):
            statement = block[i]
            if (
                statement.type == AST_STATEMENT.AST_STATEMENT_IF
                and len(statement.assignment.expressions) == 1
                and len(statement.block) == 1
                and statement.block[0].type == AST_STATEMENT.AST_STATEMENT_IF
                and len(statement.block[0].assignment.expressions) == 1
            ):
                inner_if = statement.block[0]
                merged = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION)
                merged.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_AND
                merged.binary_operation.left_operand = statement.assignment.expressions[-1]
                merged.binary_operation.right_operand = inner_if.assignment.expressions[-1]
                statement.assignment.expressions[-1] = merged
                statement.block = inner_if.block
                continue
            i += 1

    def _collapse_bool_temp_returns(self, function: Function, block: list[Statement]) -> None:
        def get_bool_constant(expression: Optional[Expression]) -> Optional[bool]:
            if (
                expression is None
                or expression.type != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
            ):
                return None
            if expression.constant.type == AST_CONSTANT.AST_CONSTANT_TRUE:
                return True
            if expression.constant.type == AST_CONSTANT.AST_CONSTANT_FALSE:
                return False
            return None

        def parse_bool_if_for_slot(
            if_statement: Statement, else_statement: Optional[Statement], slot: int
        ) -> Optional[tuple[Expression, bool, bool]]:
            if (
                if_statement.type != AST_STATEMENT.AST_STATEMENT_IF
                or len(if_statement.assignment.expressions) != 1
            ):
                return None

            then_candidates: list[Statement] = []
            else_candidates: list[Statement] = []
            if else_statement is not None:
                then_candidates = [
                    child
                    for child in if_statement.block
                    if child.type != AST_STATEMENT.AST_STATEMENT_EMPTY
                ]
                else_candidates = [
                    nested
                    for nested in else_statement.block
                    if nested.type != AST_STATEMENT.AST_STATEMENT_EMPTY
                ]
            else:
                seen_inline_else = False
                for child in if_statement.block:
                    if child.type == AST_STATEMENT.AST_STATEMENT_EMPTY:
                        continue
                    if child.type == AST_STATEMENT.AST_STATEMENT_ELSE:
                        seen_inline_else = True
                        else_candidates = [
                            nested
                            for nested in child.block
                            if nested.type != AST_STATEMENT.AST_STATEMENT_EMPTY
                        ]
                        break
                    then_candidates.append(child)
                if not seen_inline_else:
                    return None

            if len(then_candidates) != 1 or len(else_candidates) != 1:
                return None

            then_assignment = then_candidates[0]
            else_assignment = else_candidates[0]
            if (
                then_assignment.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or else_assignment.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or len(then_assignment.assignment.variables) != 1
                or len(else_assignment.assignment.variables) != 1
                or then_assignment.assignment.variables[-1].type
                != AST_VARIABLE.AST_VARIABLE_SLOT
                or else_assignment.assignment.variables[-1].type
                != AST_VARIABLE.AST_VARIABLE_SLOT
                or then_assignment.assignment.variables[-1].slot != slot
                or else_assignment.assignment.variables[-1].slot != slot
                or len(then_assignment.assignment.expressions) != 1
                or len(else_assignment.assignment.expressions) != 1
            ):
                return None

            then_bool = get_bool_constant(then_assignment.assignment.expressions[-1])
            else_bool = get_bool_constant(else_assignment.assignment.expressions[-1])
            if then_bool is None or else_bool is None or then_bool == else_bool:
                return None

            return (if_statement.assignment.expressions[-1], then_bool, else_bool)

        for statement in block:
            if statement.block:
                self._collapse_bool_temp_returns(function, statement.block)

        i = 0
        while i < len(block):
            declaration = block[i]
            if (
                declaration.type != AST_STATEMENT.AST_STATEMENT_DECLARATION
                or len(declaration.assignment.variables) != 1
                or declaration.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                i += 1
                continue

            if declaration.assignment.expressions:
                if (
                    len(declaration.assignment.expressions) != 1
                    or declaration.assignment.expressions[-1].type
                    != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                    or declaration.assignment.expressions[-1].constant.type
                    != AST_CONSTANT.AST_CONSTANT_NIL
                ):
                    i += 1
                    continue

            slot = declaration.assignment.variables[-1].slot
            slot_scope = declaration.assignment.variables[-1].slot_scope

            if_index = i + 1
            while if_index < len(block) and block[if_index].type == AST_STATEMENT.AST_STATEMENT_EMPTY:
                if_index += 1
            if if_index >= len(block):
                i += 1
                continue

            if_statement = block[if_index]
            else_index = if_index + 1
            while else_index < len(block) and block[else_index].type == AST_STATEMENT.AST_STATEMENT_EMPTY:
                else_index += 1
            else_statement: Optional[Statement] = None
            return_start_index = if_index + 1
            if else_index < len(block) and block[else_index].type == AST_STATEMENT.AST_STATEMENT_ELSE:
                else_statement = block[else_index]
                return_start_index = else_index + 1

            parsed = parse_bool_if_for_slot(if_statement, else_statement, slot)
            if parsed is None:
                i += 1
                continue

            condition_expression, then_bool, else_bool = parsed

            return_index = return_start_index
            while (
                return_index < len(block)
                and block[return_index].type == AST_STATEMENT.AST_STATEMENT_EMPTY
            ):
                return_index += 1
            if return_index >= len(block):
                i += 1
                continue

            return_statement = block[return_index]
            if (
                return_statement.type != AST_STATEMENT.AST_STATEMENT_RETURN
                or len(return_statement.assignment.expressions) != 1
                or return_statement.assignment.expressions[-1].type
                != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                or return_statement.assignment.expressions[-1].variable.type
                != AST_VARIABLE.AST_VARIABLE_SLOT
                or return_statement.assignment.expressions[-1].variable.slot != slot
            ):
                i += 1
                continue

            replacement = self._clone_expression_deep(condition_expression)
            if not then_bool and else_bool:
                replacement = self._negate_condition_expression(replacement)
            replacement = self._simplify_safe_double_not_expression(replacement)
            return_statement.assignment.expressions[-1] = replacement
            if _verbose_enabled:
                verbose_log(
                    "collapse_bool_temp_returns: slot="
                    + str(slot)
                    + ", function_id="
                    + str(function.id)
                )
            if (
                function.is_valid_label(declaration.instruction.label)
                and not function.is_valid_label(return_statement.instruction.label)
            ):
                return_statement.instruction.label = declaration.instruction.label

            if slot_scope is not None:
                function.slot_scope_collector.remove_scope(slot, slot_scope)

            if else_statement is not None:
                del block[else_index]
            del block[if_index]
            del block[i]
            continue

    def _fold_if_condition_bool_control_flow_returns(
        self, function: Function, block: list[Statement]
    ) -> None:
        def get_single_slot_bool_assignment(
            statement: Statement,
        ) -> Optional[tuple[AstVariable, bool]]:
            if statement.type not in (
                AST_STATEMENT.AST_STATEMENT_DECLARATION,
                AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
            ):
                return None
            if (
                len(statement.assignment.variables) != 1
                or len(statement.assignment.expressions) != 1
                or statement.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                return None
            bool_value = self._bool_constant_value(statement.assignment.expressions[-1])
            if bool_value is None:
                return None
            return (statement.assignment.variables[-1], bool_value)

        for statement in block:
            if statement.block:
                self._fold_if_condition_bool_control_flow_returns(function, statement.block)

        i = 0
        while i + 5 < len(block):
            if_statement = block[i]
            do_statement = block[i + 1]
            true_label_statement = block[i + 2]
            true_assignment_statement = block[i + 3]
            return_label_statement = block[i + 4]
            return_statement = block[i + 5]

            if (
                if_statement.type != AST_STATEMENT.AST_STATEMENT_IF
                or len(if_statement.assignment.expressions) != 1
                or do_statement.type != AST_STATEMENT.AST_STATEMENT_DO
                or true_label_statement.type != AST_STATEMENT.AST_STATEMENT_LABEL
                or true_assignment_statement.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or return_label_statement.type != AST_STATEMENT.AST_STATEMENT_LABEL
                or return_statement.type != AST_STATEMENT.AST_STATEMENT_RETURN
                or len(return_statement.assignment.expressions) != 1
                or return_statement.assignment.expressions[-1].type
                != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                or return_statement.assignment.expressions[-1].variable.type
                != AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                i += 1
                continue

            do_children = [
                statement
                for statement in do_statement.block
                if statement.type != AST_STATEMENT.AST_STATEMENT_EMPTY
            ]
            if len(do_children) != 2:
                i += 1
                continue

            false_assignment_statement = do_children[0]
            goto_statement = do_children[1]
            false_assignment = get_single_slot_bool_assignment(false_assignment_statement)
            true_assignment = get_single_slot_bool_assignment(true_assignment_statement)

            if (
                false_assignment is None
                or true_assignment is None
                or goto_statement.type
                not in (
                    AST_STATEMENT.AST_STATEMENT_GOTO,
                    AST_STATEMENT.AST_STATEMENT_BREAK,
                )
                or goto_statement.instruction.type != BC_OP.BC_OP_JMP
                or len(true_assignment_statement.assignment.variables) != 1
                or len(true_assignment_statement.assignment.expressions) != 1
            ):
                i += 1
                continue

            false_variable, false_bool = false_assignment
            true_variable, true_bool = true_assignment
            if false_bool == true_bool:
                i += 1
                continue

            if (
                false_variable.slot != true_variable.slot
                or return_statement.assignment.expressions[-1].variable.slot
                != false_variable.slot
                or goto_statement.instruction.target != return_statement.instruction.id
                or not function.is_valid_label(true_label_statement.instruction.label)
                or true_assignment_statement.instruction.label
                != true_label_statement.instruction.label
                or not function.is_valid_label(return_label_statement.instruction.label)
                or return_statement.instruction.label
                != return_label_statement.instruction.label
            ):
                i += 1
                continue

            if_children = [
                statement
                for statement in if_statement.block
                if statement.type != AST_STATEMENT.AST_STATEMENT_EMPTY
            ]
            if not (1 <= len(if_children) <= 2):
                i += 1
                continue

            prep_declaration: Optional[Statement] = None
            condition_statement: Optional[Statement] = None
            if len(if_children) == 1:
                condition_statement = if_children[0]
            else:
                prep_declaration = if_children[0]
                condition_statement = if_children[1]

            if (
                condition_statement.type != AST_STATEMENT.AST_STATEMENT_CONDITION
                or condition_statement.assignment.variables
                or len(condition_statement.assignment.expressions) != 1
                or condition_statement.instruction.target
                != true_assignment_statement.instruction.id
            ):
                i += 1
                continue

            branch_expression = self._clone_expression_deep(
                condition_statement.assignment.expressions[-1]
            )
            if false_bool:
                branch_expression = self._simplify_safe_double_not_expression(
                    branch_expression
                )
            else:
                branch_expression = self._negate_condition_expression(branch_expression)
                branch_expression = self._simplify_safe_double_not_expression(
                    branch_expression
                )

            if prep_declaration is not None:
                if (
                    prep_declaration.type != AST_STATEMENT.AST_STATEMENT_DECLARATION
                    or len(prep_declaration.assignment.variables) != 1
                    or len(prep_declaration.assignment.expressions) != 1
                    or prep_declaration.assignment.variables[-1].type
                    != AST_VARIABLE.AST_VARIABLE_SLOT
                ):
                    i += 1
                    continue
                prep_variable = prep_declaration.assignment.variables[-1]
                replaced = self._replace_slot_in_expression(
                    branch_expression,
                    prep_variable.slot,
                    prep_declaration.assignment.expressions[-1],
                    prep_variable.slot_scope,
                )
                if replaced != 1:
                    i += 1
                    continue
                if prep_variable.slot_scope is not None:
                    function.slot_scope_collector.remove_scope(
                        prep_variable.slot, prep_variable.slot_scope
                    )

            outer_expression = self._clone_expression_deep(
                if_statement.assignment.expressions[-1]
            )
            if false_bool:
                final_expression = self.new_expression(
                    AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                )
                final_expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_OR
                final_expression.binary_operation.left_operand = (
                    self._negate_condition_expression(outer_expression)
                )
                final_expression.binary_operation.right_operand = branch_expression
            else:
                final_expression = self.new_expression(
                    AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                )
                final_expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_AND
                final_expression.binary_operation.left_operand = outer_expression
                final_expression.binary_operation.right_operand = branch_expression

            return_statement.assignment.expressions[-1] = (
                self._simplify_safe_double_not_expression(final_expression)
            )
            if (
                function.is_valid_label(if_statement.instruction.label)
                and not function.is_valid_label(return_statement.instruction.label)
            ):
                return_statement.instruction.label = if_statement.instruction.label

            function.remove_jump(
                if_statement.instruction.id, if_statement.instruction.target
            )
            function.remove_jump(
                condition_statement.instruction.id, condition_statement.instruction.target
            )
            function.remove_jump(
                condition_statement.instruction.id + 1,
                condition_statement.instruction.target,
            )
            function.remove_jump(
                goto_statement.instruction.id, goto_statement.instruction.target
            )

            if false_variable.slot_scope is not None:
                function.slot_scope_collector.remove_scope(
                    false_variable.slot, false_variable.slot_scope
                )
            if (
                true_variable.slot_scope is not None
                and true_variable.slot_scope is not false_variable.slot_scope
            ):
                function.slot_scope_collector.remove_scope(
                    true_variable.slot, true_variable.slot_scope
                )

            block[i] = return_statement
            del block[i + 1 : i + 6]

    def _inline_declaration_return_temps(
        self, function: Function, block: list[Statement]
    ) -> None:
        for statement in block:
            if statement.block:
                self._inline_declaration_return_temps(function, statement.block)

        i = 0
        while i + 1 < len(block):
            declaration = block[i]
            return_statement = block[i + 1]
            if (
                declaration.type != AST_STATEMENT.AST_STATEMENT_DECLARATION
                or return_statement.type != AST_STATEMENT.AST_STATEMENT_RETURN
                or len(declaration.assignment.variables) != 1
                or len(declaration.assignment.expressions) != 1
                or len(return_statement.assignment.expressions) != 1
                or declaration.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
                or declaration.assignment.expressions[-1].type
                != AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                or return_statement.assignment.expressions[-1].type
                != AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
            ):
                i += 1
                continue

            rewritten_return_expression = self._clone_expression_deep(
                return_statement.assignment.expressions[-1]
            )
            replaced = self._replace_slot_in_expression(
                rewritten_return_expression,
                declaration.assignment.variables[-1].slot,
                declaration.assignment.expressions[-1],
                declaration.assignment.variables[-1].slot_scope,
            )
            if replaced != 1:
                i += 1
                continue

            return_statement.assignment.expressions[-1] = rewritten_return_expression
            if (
                function.is_valid_label(declaration.instruction.label)
                and not function.is_valid_label(return_statement.instruction.label)
            ):
                return_statement.instruction.label = declaration.instruction.label
            if declaration.assignment.variables[-1].slot_scope is not None:
                function.slot_scope_collector.remove_scope(
                    declaration.assignment.variables[-1].slot,
                    declaration.assignment.variables[-1].slot_scope,
                )
            del block[i]

    def _is_single_value_return_safe_expression(
        self, expression: Optional[Expression]
    ) -> bool:
        if expression is None:
            return False
        if expression.type in (
            AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL,
            AST_EXPRESSION.AST_EXPRESSION_VARARG,
        ):
            # `return f()` can return multiple values; keep temp-based one-value semantics.
            return False
        return True

    @staticmethod
    def _is_nil_only_declaration(statement: Statement) -> bool:
        if statement.type != AST_STATEMENT.AST_STATEMENT_DECLARATION:
            return False
        if not statement.assignment.expressions:
            return True
        return (
            len(statement.assignment.expressions) == 1
            and statement.assignment.expressions[-1].type
            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
            and statement.assignment.expressions[-1].constant.type
            == AST_CONSTANT.AST_CONSTANT_NIL
        )

    @staticmethod
    def _return_expression_matches_slot(
        expression: Optional[Expression], slot: int, slot_scope: Optional[ScopeCell]
    ) -> bool:
        if (
            expression is None
            or expression.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
            or expression.variable.type != AST_VARIABLE.AST_VARIABLE_SLOT
            or expression.variable.slot != slot
        ):
            return False
        if slot_scope is None:
            return True
        return (
            expression.variable.slot_scope is slot_scope
            or expression.variable.slot_scope is None
        )

    def _inline_declaration_return_aliases(
        self, function: Function, block: list[Statement]
    ) -> None:
        for statement in block:
            if statement.block:
                self._inline_declaration_return_aliases(function, statement.block)

        i = 0
        while i < len(block):
            if i + 1 < len(block):
                declaration = block[i]
                return_statement = block[i + 1]
                if (
                    declaration.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and not declaration.assignment.forward_declaration
                    and return_statement.type == AST_STATEMENT.AST_STATEMENT_RETURN
                    and len(declaration.assignment.variables) == 1
                    and len(declaration.assignment.expressions) == 1
                    and len(return_statement.assignment.expressions) == 1
                    and declaration.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and self._is_single_value_return_safe_expression(
                        declaration.assignment.expressions[-1]
                    )
                    and self._return_expression_matches_slot(
                        return_statement.assignment.expressions[-1],
                        declaration.assignment.variables[-1].slot,
                        declaration.assignment.variables[-1].slot_scope,
                    )
                ):
                    return_statement.assignment.expressions[-1] = self._clone_expression_deep(
                        declaration.assignment.expressions[-1]
                    )
                    if function.is_valid_label(declaration.instruction.label):
                        return_statement.instruction.label = declaration.instruction.label
                    if declaration.assignment.variables[-1].slot_scope is not None:
                        function.slot_scope_collector.remove_scope(
                            declaration.assignment.variables[-1].slot,
                            declaration.assignment.variables[-1].slot_scope,
                        )
                    del block[i]
                    continue

            if i + 2 < len(block):
                declaration = block[i]
                assignment = block[i + 1]
                return_statement = block[i + 2]
                if (
                    declaration.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                    and not declaration.assignment.forward_declaration
                    and self._is_nil_only_declaration(declaration)
                    and assignment.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(declaration.assignment.variables) == 1
                    and len(assignment.assignment.variables) == 1
                    and len(assignment.assignment.expressions) == 1
                    and len(return_statement.assignment.expressions) == 1
                    and declaration.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and assignment.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and declaration.assignment.variables[-1].slot
                    == assignment.assignment.variables[-1].slot
                    and (
                        declaration.assignment.variables[-1].slot_scope
                        is assignment.assignment.variables[-1].slot_scope
                        or declaration.assignment.variables[-1].slot_scope is None
                        or assignment.assignment.variables[-1].slot_scope is None
                    )
                    and return_statement.type == AST_STATEMENT.AST_STATEMENT_RETURN
                    and self._is_single_value_return_safe_expression(
                        assignment.assignment.expressions[-1]
                    )
                    and self._return_expression_matches_slot(
                        return_statement.assignment.expressions[-1],
                        declaration.assignment.variables[-1].slot,
                        declaration.assignment.variables[-1].slot_scope,
                    )
                    and not function.is_valid_label(assignment.instruction.label)
                ):
                    return_statement.assignment.expressions[-1] = self._clone_expression_deep(
                        assignment.assignment.expressions[-1]
                    )
                    if function.is_valid_label(declaration.instruction.label):
                        return_statement.instruction.label = declaration.instruction.label
                    if declaration.assignment.variables[-1].slot_scope is not None:
                        function.slot_scope_collector.remove_scope(
                            declaration.assignment.variables[-1].slot,
                            declaration.assignment.variables[-1].slot_scope,
                        )
                    del block[i : i + 2]
                    continue

            i += 1

    def _fold_short_circuit_if_assignments(
        self, function: Function, block: list[Statement]
    ) -> None:
        def is_empty_or_nil_declaration(statement: Statement) -> bool:
            if statement.type != AST_STATEMENT.AST_STATEMENT_DECLARATION:
                return False
            if len(statement.assignment.variables) != 1:
                return False
            if not statement.assignment.expressions:
                return True
            return (
                len(statement.assignment.expressions) == 1
                and statement.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                and statement.assignment.expressions[-1].constant.type
                == AST_CONSTANT.AST_CONSTANT_NIL
            )

        def get_declaration_from_container(
            statement: Statement,
        ) -> tuple[Optional[Statement], bool]:
            if is_empty_or_nil_declaration(statement):
                return statement, False
            if statement.type != AST_STATEMENT.AST_STATEMENT_DO:
                return None, False
            non_empty_children = [
                child
                for child in statement.block
                if child.type != AST_STATEMENT.AST_STATEMENT_EMPTY
            ]
            if len(non_empty_children) != 1:
                return None, False
            child = non_empty_children[0]
            if not is_empty_or_nil_declaration(child):
                return None, False
            return child, True

        def is_runtime_noop(statement: Statement) -> bool:
            if statement.type == AST_STATEMENT.AST_STATEMENT_EMPTY:
                return True
            if statement.type == AST_STATEMENT.AST_STATEMENT_LABEL:
                return True
            if is_empty_or_nil_declaration(statement):
                return True
            if statement.type == AST_STATEMENT.AST_STATEMENT_DO:
                return all(is_runtime_noop(child) for child in statement.block)
            return False

        def statement_single_slot_assignment(
            statement: Statement,
        ) -> tuple[Optional[AstVariable], Optional[Expression]]:
            if (
                statement.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or len(statement.assignment.variables) != 1
                or len(statement.assignment.expressions) != 1
                or statement.assignment.variables[-1].type
                != AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                return None, None
            return statement.assignment.variables[-1], statement.assignment.expressions[-1]

        def get_condition_guard_slot(
            condition_statement: Statement,
        ) -> tuple[int, bool]:
            if (
                not condition_statement.assignment.expressions
                or len(condition_statement.assignment.expressions) != 1
            ):
                return INVALID_ID, False
            guard_expression = condition_statement.assignment.expressions[-1]
            if (
                guard_expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                and guard_expression.variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                return guard_expression.variable.slot, False
            if (
                guard_expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION
                and guard_expression.unary_operation.type == AST_UNARY_OPERATION.AST_UNARY_NOT
                and guard_expression.unary_operation.operand is not None
                and guard_expression.unary_operation.operand.type
                == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                and guard_expression.unary_operation.operand.variable.type
                == AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                return guard_expression.unary_operation.operand.variable.slot, True
            return INVALID_ID, False

        for statement in block:
            if statement.block:
                self._fold_short_circuit_if_assignments(function, statement.block)

        i = 0
        while i + 2 < len(block):
            declaration_container = block[i]
            declaration, is_do_container = get_declaration_from_container(
                declaration_container
            )
            if declaration is None:
                i += 1
                continue

            target_variable = declaration.assignment.variables[-1]
            if target_variable.type != AST_VARIABLE.AST_VARIABLE_SLOT:
                i += 1
                continue

            if_statement = block[i + 1]
            if if_statement.type != AST_STATEMENT.AST_STATEMENT_IF or len(
                if_statement.assignment.expressions
            ) != 1:
                i += 1
                continue

            if_children = [
                child
                for child in if_statement.block
                if child.type != AST_STATEMENT.AST_STATEMENT_EMPTY
            ]
            if len(if_children) != 2:
                i += 1
                continue

            true_assignment = if_children[0]
            guard_condition = if_children[1]
            true_variable, true_expression = statement_single_slot_assignment(
                true_assignment
            )
            guard_slot, _ = get_condition_guard_slot(guard_condition)
            if (
                true_variable is None
                or true_expression is None
                or guard_condition.type != AST_STATEMENT.AST_STATEMENT_CONDITION
                or guard_condition.instruction.type != BC_OP.BC_OP_IST
                or guard_condition.assignment.variables
                or len(guard_condition.assignment.expressions) != 1
                or true_variable.slot != target_variable.slot
                or guard_slot != target_variable.slot
            ):
                i += 1
                continue

            fallback_index = i + 2
            while (
                fallback_index < len(block)
                and block[fallback_index].type == AST_STATEMENT.AST_STATEMENT_EMPTY
            ):
                fallback_index += 1
            if fallback_index >= len(block):
                i += 1
                continue

            fallback_statement = block[fallback_index]
            fallback_variable, fallback_expression = statement_single_slot_assignment(
                fallback_statement
            )
            if (
                fallback_variable is None
                or fallback_expression is None
                or fallback_variable.slot != target_variable.slot
            ):
                i += 1
                continue

            label_index = INVALID_ID
            for j in range(fallback_index + 1, len(block)):
                candidate = block[j]
                if candidate.type != AST_STATEMENT.AST_STATEMENT_LABEL:
                    continue
                if not function.is_valid_label(candidate.instruction.label):
                    continue
                if (
                    function.labels[candidate.instruction.label].target
                    == guard_condition.instruction.target
                ):
                    label_index = j
                    break

            if label_index == INVALID_ID:
                i += 1
                continue

            if any(
                not is_runtime_noop(block[j])
                for j in range(fallback_index + 1, label_index)
            ):
                i += 1
                continue

            and_expression = self.new_expression(
                AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
            )
            and_expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_AND
            and_expression.binary_operation.left_operand = self._clone_expression_deep(
                if_statement.assignment.expressions[-1]
            )
            and_expression.binary_operation.right_operand = self._clone_expression_deep(
                true_expression
            )

            or_expression = self.new_expression(
                AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
            )
            or_expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_OR
            or_expression.binary_operation.left_operand = and_expression
            or_expression.binary_operation.right_operand = self._clone_expression_deep(
                fallback_expression
            )

            declaration.assignment.expressions = [or_expression]
            if is_do_container:
                block[i] = declaration
            if (
                function.is_valid_label(if_statement.instruction.label)
                and not function.is_valid_label(declaration.instruction.label)
            ):
                declaration.instruction.label = if_statement.instruction.label

            function.remove_jump(
                if_statement.instruction.id, if_statement.instruction.target
            )
            function.remove_jump(
                if_statement.instruction.id + 1, if_statement.instruction.target
            )
            function.remove_jump(
                guard_condition.instruction.id, guard_condition.instruction.target
            )
            function.remove_jump(
                guard_condition.instruction.id + 1, guard_condition.instruction.target
            )

            del block[i + 1 : fallback_index + 1]

            for j in range(len(block) - 1, i, -1):
                if (
                    block[j].type == AST_STATEMENT.AST_STATEMENT_LABEL
                    and not function.is_valid_label(block[j].instruction.label)
                ):
                    del block[j]

            continue

        i = 0
        while i + 3 < len(block):
            declaration_container = block[i]
            declaration, is_do_container = get_declaration_from_container(
                declaration_container
            )
            if declaration is None:
                i += 1
                continue
            if (
                len(declaration.assignment.variables) != 1
                or declaration.assignment.variables[-1].type
                != AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                i += 1
                continue

            target_slot = declaration.assignment.variables[-1].slot
            branch_items: list[tuple[int, Statement, Statement, Expression]] = []
            chain_target = INVALID_ID
            scan_index = i + 1
            while scan_index < len(block):
                while (
                    scan_index < len(block)
                    and block[scan_index].type == AST_STATEMENT.AST_STATEMENT_EMPTY
                ):
                    scan_index += 1
                if scan_index >= len(block):
                    break

                if_statement = block[scan_index]
                if (
                    if_statement.type != AST_STATEMENT.AST_STATEMENT_IF
                    or len(if_statement.assignment.expressions) != 1
                ):
                    break

                if_children = [
                    child
                    for child in if_statement.block
                    if child.type != AST_STATEMENT.AST_STATEMENT_EMPTY
                ]
                if len(if_children) != 2:
                    break
                true_assignment = if_children[0]
                guard_condition = if_children[1]
                true_variable, true_expression = statement_single_slot_assignment(
                    true_assignment
                )
                guard_slot, _ = get_condition_guard_slot(guard_condition)
                if (
                    true_variable is None
                    or true_expression is None
                    or true_variable.slot != target_slot
                    or guard_condition.type != AST_STATEMENT.AST_STATEMENT_CONDITION
                    or guard_condition.instruction.type != BC_OP.BC_OP_IST
                    or guard_condition.assignment.variables
                    or len(guard_condition.assignment.expressions) != 1
                    or guard_slot != target_slot
                ):
                    break

                if chain_target == INVALID_ID:
                    chain_target = guard_condition.instruction.target
                elif chain_target != guard_condition.instruction.target:
                    break
                branch_items.append(
                    (scan_index, if_statement, guard_condition, true_expression)
                )
                scan_index += 1

            if len(branch_items) < 2 or chain_target == INVALID_ID:
                i += 1
                continue

            fallback_index = scan_index
            while (
                fallback_index < len(block)
                and block[fallback_index].type == AST_STATEMENT.AST_STATEMENT_EMPTY
            ):
                fallback_index += 1
            if fallback_index >= len(block):
                i += 1
                continue

            fallback_statement = block[fallback_index]
            fallback_variable, fallback_expression = statement_single_slot_assignment(
                fallback_statement
            )
            if (
                fallback_variable is None
                or fallback_expression is None
                or fallback_variable.slot != target_slot
            ):
                i += 1
                continue

            label_index = INVALID_ID
            for j in range(fallback_index + 1, len(block)):
                candidate = block[j]
                if candidate.type != AST_STATEMENT.AST_STATEMENT_LABEL:
                    continue
                if not function.is_valid_label(candidate.instruction.label):
                    continue
                if function.labels[candidate.instruction.label].target == chain_target:
                    label_index = j
                    break
            if label_index == INVALID_ID:
                i += 1
                continue
            if any(
                not is_runtime_noop(block[j])
                for j in range(fallback_index + 1, label_index)
            ):
                i += 1
                continue

            combined_expression = self._clone_expression_deep(fallback_expression)
            for _, if_statement, _, true_expression in reversed(branch_items):
                and_expression = self.new_expression(
                    AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                )
                and_expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_AND
                and_expression.binary_operation.left_operand = self._clone_expression_deep(
                    if_statement.assignment.expressions[-1]
                )
                and_expression.binary_operation.right_operand = self._clone_expression_deep(
                    true_expression
                )
                or_expression = self.new_expression(
                    AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                )
                or_expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_OR
                or_expression.binary_operation.left_operand = and_expression
                or_expression.binary_operation.right_operand = combined_expression
                combined_expression = or_expression

            declaration.assignment.expressions = [combined_expression]
            if is_do_container:
                block[i] = declaration
            first_if_statement = branch_items[0][1]
            if (
                function.is_valid_label(first_if_statement.instruction.label)
                and not function.is_valid_label(declaration.instruction.label)
            ):
                declaration.instruction.label = first_if_statement.instruction.label

            for _, if_statement, guard_condition, _ in branch_items:
                function.remove_jump(
                    if_statement.instruction.id, if_statement.instruction.target
                )
                function.remove_jump(
                    if_statement.instruction.id + 1, if_statement.instruction.target
                )
                function.remove_jump(
                    guard_condition.instruction.id, guard_condition.instruction.target
                )
                function.remove_jump(
                    guard_condition.instruction.id + 1, guard_condition.instruction.target
                )

            del block[i + 1 : fallback_index + 1]
            for j in range(len(block) - 1, i, -1):
                if (
                    block[j].type == AST_STATEMENT.AST_STATEMENT_LABEL
                    and not function.is_valid_label(block[j].instruction.label)
                ):
                    del block[j]
            continue

    def _fold_if_condition_jump_guards(
        self, function: Function, block: list[Statement]
    ) -> None:
        def is_side_effect_free_expression(expression: Optional[Expression]) -> bool:
            if expression is None:
                return False
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
                return False
            return self._expression_is_side_effect_free(expression)

        for statement in block:
            if statement.block:
                self._fold_if_condition_jump_guards(function, statement.block)

        i = 0
        while i < len(block):
            if_statement = block[i]
            if (
                if_statement.type != AST_STATEMENT.AST_STATEMENT_IF
                or len(if_statement.assignment.expressions) != 1
            ):
                i += 1
                continue

            assignment_index = i + 1
            while (
                assignment_index < len(block)
                and block[assignment_index].type == AST_STATEMENT.AST_STATEMENT_EMPTY
            ):
                if function.is_valid_label(block[assignment_index].instruction.label):
                    assignment_index = INVALID_ID
                    break
                assignment_index += 1
            if assignment_index == INVALID_ID or assignment_index >= len(block):
                i += 1
                continue

            assignment_statement = block[assignment_index]
            if (
                assignment_statement.type not in (
                    AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                    AST_STATEMENT.AST_STATEMENT_DECLARATION,
                )
                or len(assignment_statement.assignment.variables) != 1
                or len(assignment_statement.assignment.expressions) != 1
                or function.is_valid_label(assignment_statement.instruction.label)
            ):
                i += 1
                continue

            if any(
                block[j].type != AST_STATEMENT.AST_STATEMENT_EMPTY
                for j in range(assignment_index + 1, len(block))
            ):
                i += 1
                continue

            if_children = [
                child
                for child in if_statement.block
                if child.type != AST_STATEMENT.AST_STATEMENT_EMPTY
            ]
            if len(if_children) != 2:
                i += 1
                continue

            declaration_statement = if_children[0]
            condition_statement = if_children[1]
            if (
                declaration_statement.type != AST_STATEMENT.AST_STATEMENT_DECLARATION
                or len(declaration_statement.assignment.variables) != 1
                or len(declaration_statement.assignment.expressions) != 1
                or declaration_statement.assignment.variables[-1].type
                != AST_VARIABLE.AST_VARIABLE_SLOT
                or not is_side_effect_free_expression(
                    declaration_statement.assignment.expressions[-1]
                )
                or condition_statement.type != AST_STATEMENT.AST_STATEMENT_CONDITION
                or condition_statement.assignment.variables
                or len(condition_statement.assignment.expressions) != 1
                or Ast.get_block_index_from_id(block, condition_statement.instruction.target)
                != INVALID_ID
            ):
                i += 1
                continue

            slot_variable = declaration_statement.assignment.variables[-1]
            rewritten_guard = self._clone_expression_deep(
                condition_statement.assignment.expressions[-1]
            )
            replaced = self._replace_slot_in_expression(
                rewritten_guard,
                slot_variable.slot,
                declaration_statement.assignment.expressions[-1],
                slot_variable.slot_scope,
            )
            if replaced == 0 and slot_variable.slot_scope is not None:
                replaced = self._replace_slot_in_expression(
                    rewritten_guard,
                    slot_variable.slot,
                    declaration_statement.assignment.expressions[-1],
                    None,
                )
            if replaced != 1:
                i += 1
                continue

            and_expression = self.new_expression(
                AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
            )
            and_expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_AND
            and_expression.binary_operation.left_operand = self._clone_expression_deep(
                if_statement.assignment.expressions[-1]
            )
            and_expression.binary_operation.right_operand = rewritten_guard

            merged_condition = self.new_expression(
                AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION
            )
            merged_condition.unary_operation.type = AST_UNARY_OPERATION.AST_UNARY_NOT
            merged_condition.unary_operation.operand = and_expression
            merged_condition = self._simplify_safe_double_not_expression(
                merged_condition
            )

            if_statement.assignment.expressions[-1] = merged_condition
            if_statement.block = [assignment_statement]
            if (
                function.is_valid_label(declaration_statement.instruction.label)
                and not function.is_valid_label(assignment_statement.instruction.label)
            ):
                assignment_statement.instruction.label = (
                    declaration_statement.instruction.label
                )

            if slot_variable.slot_scope is not None:
                function.slot_scope_collector.remove_scope(
                    slot_variable.slot, slot_variable.slot_scope
                )
            function.remove_jump(
                condition_statement.instruction.id, condition_statement.instruction.target
            )
            function.remove_jump(
                condition_statement.instruction.id + 1,
                condition_statement.instruction.target,
            )

            del block[assignment_index]
            continue

    def _inline_pure_call_argument_temps(
        self, function: Function, block: list[Statement]
    ) -> None:
        def expression_slot_use_count(
            expression: Optional[Expression],
            slot: int,
            target_scope: Optional[ScopeCell],
        ) -> int:
            if expression is None:
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
                variable = expression.variable
                if variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    if variable.slot != slot:
                        return 0
                    if target_scope is None:
                        return 1
                    return 1 if variable.slot_scope is target_scope else 0
                if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    return expression_slot_use_count(
                        variable.table, slot, target_scope
                    ) + expression_slot_use_count(variable.table_index, slot, target_scope)
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
                function_call = expression.function_call
                uses = expression_slot_use_count(function_call.function, slot, target_scope)
                uses += expression_slot_use_count(
                    function_call.multres_argument, slot, target_scope
                )
                for argument in function_call.arguments:
                    uses += expression_slot_use_count(argument, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
                uses = expression_slot_use_count(
                    expression.table.multres_field, slot, target_scope
                )
                for field in expression.table.fields:
                    uses += expression_slot_use_count(field.key, slot, target_scope)
                    uses += expression_slot_use_count(field.value, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
                return expression_slot_use_count(
                    expression.binary_operation.left_operand, slot, target_scope
                ) + expression_slot_use_count(
                    expression.binary_operation.right_operand, slot, target_scope
                )
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
                return expression_slot_use_count(
                    expression.unary_operation.operand, slot, target_scope
                )
            return 0

        def statement_slot_use_count(
            statement: Statement, slot: int, target_scope: Optional[ScopeCell]
        ) -> int:
            uses = expression_slot_use_count(
                statement.assignment.multres_return, slot, target_scope
            )
            for expression in statement.assignment.expressions:
                uses += expression_slot_use_count(expression, slot, target_scope)
            for variable in statement.assignment.variables:
                if variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    continue
                uses += expression_slot_use_count(variable.table, slot, target_scope)
                uses += expression_slot_use_count(variable.table_index, slot, target_scope)
            for nested in statement.block:
                uses += statement_slot_use_count(nested, slot, target_scope)
            return uses

        def statement_writes_slot(
            statement: Statement, slot: int, target_scope: Optional[ScopeCell]
        ) -> bool:
            for variable in statement.assignment.variables:
                if variable.type != AST_VARIABLE.AST_VARIABLE_SLOT:
                    continue
                if variable.slot != slot:
                    continue
                if target_scope is None or variable.slot_scope is target_scope:
                    return True
            return False

        def clone_statement_preserving_scopes(statement: Statement) -> Statement:
            memo: dict[int, object] = {}

            for info in function.slot_scope_collector.slot_infos:
                if info.active_slot_scope is not None:
                    memo[id(info.active_slot_scope)] = info.active_slot_scope
                    if info.active_slot_scope.scope is not None:
                        memo[id(info.active_slot_scope.scope)] = info.active_slot_scope.scope
                for cell in info.slot_scopes:
                    memo[id(cell)] = cell
                    if cell.scope is not None:
                        memo[id(cell.scope)] = cell.scope

            for upvalue in function.upvalues:
                if upvalue.slot_scope is None:
                    continue
                memo[id(upvalue.slot_scope)] = upvalue.slot_scope
                if upvalue.slot_scope.scope is not None:
                    memo[id(upvalue.slot_scope.scope)] = upvalue.slot_scope.scope

            return copy.deepcopy(statement, memo)

        def is_pure_expression(expression: Optional[Expression]) -> bool:
            if expression is None:
                return False
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
                return False
            return self._expression_is_side_effect_free(expression)

        def is_nil_only_single_slot_declaration(statement: Statement) -> bool:
            if statement.type != AST_STATEMENT.AST_STATEMENT_DECLARATION:
                return False
            if len(statement.assignment.variables) != 1:
                return False
            if not statement.assignment.expressions:
                return True
            return (
                len(statement.assignment.expressions) == 1
                and statement.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                and statement.assignment.expressions[-1].constant.type
                == AST_CONSTANT.AST_CONSTANT_NIL
            )

        def get_single_slot_pure_definition(
            statement: Statement,
        ) -> tuple[Optional[AstVariable], Optional[Expression], bool]:
            allowed_definition_expression_types = {
                AST_EXPRESSION.AST_EXPRESSION_CONSTANT,
                AST_EXPRESSION.AST_EXPRESSION_VARIABLE,
                AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION,
                AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION,
            }
            if statement.type not in (
                AST_STATEMENT.AST_STATEMENT_DECLARATION,
                AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
            ):
                return None, None, False
            if (
                len(statement.assignment.variables) != 1
                or len(statement.assignment.expressions) != 1
                or statement.assignment.variables[-1].type
                != AST_VARIABLE.AST_VARIABLE_SLOT
                or statement.assignment.expressions[-1].type
                not in allowed_definition_expression_types
                or not is_pure_expression(statement.assignment.expressions[-1])
            ):
                return None, None, False
            return (
                statement.assignment.variables[-1],
                statement.assignment.expressions[-1],
                statement.type == AST_STATEMENT.AST_STATEMENT_DECLARATION,
            )

        def is_call_target_statement(statement: Statement) -> bool:
            if (
                statement.type
                in (
                    AST_STATEMENT.AST_STATEMENT_DECLARATION,
                    AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                    AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL,
                )
                and len(statement.assignment.expressions) == 1
                and statement.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
            ):
                return True
            return False

        for statement in block:
            if statement.block:
                self._inline_pure_call_argument_temps(function, statement.block)

        i = 0
        while i < len(block):
            definition = block[i]
            definition_variable, definition_expression, definition_is_declaration = (
                get_single_slot_pure_definition(definition)
            )
            if (
                definition_variable is None
                or definition_expression is None
                or function.is_valid_label(definition.instruction.label)
            ):
                i += 1
                continue

            slot = definition_variable.slot
            slot_scope = definition_variable.slot_scope
            inline_applied = False

            for target_index in range(i + 1, min(len(block), i + 8)):
                target_statement = block[target_index]
                if function.is_valid_label(target_statement.instruction.label):
                    break
                if not is_call_target_statement(target_statement):
                    continue

                can_cross = True
                for middle_index in range(i + 1, target_index):
                    middle_statement = block[middle_index]
                    if middle_statement.type == AST_STATEMENT.AST_STATEMENT_EMPTY:
                        continue
                    middle_variable, middle_expression, _ = (
                        get_single_slot_pure_definition(middle_statement)
                    )
                    if (
                        function.is_valid_label(middle_statement.instruction.label)
                        or statement_slot_use_count(middle_statement, slot, slot_scope)
                        or statement_writes_slot(middle_statement, slot, slot_scope)
                        or (
                            middle_variable is None
                            and not is_nil_only_single_slot_declaration(
                                middle_statement
                            )
                        )
                    ):
                        can_cross = False
                        break

                if not can_cross:
                    break

                uses_in_target = statement_slot_use_count(
                    target_statement, slot, slot_scope
                )
                replacement_scope = slot_scope
                if uses_in_target == 0 and slot_scope is not None:
                    uses_in_target = statement_slot_use_count(
                        target_statement, slot, None
                    )
                    replacement_scope = None
                if uses_in_target != 1:
                    continue

                rewritten_target = clone_statement_preserving_scopes(target_statement)
                replaced = self._replace_slot_in_statement(
                    rewritten_target,
                    slot,
                    definition_expression,
                    replacement_scope,
                )
                if replaced != 1:
                    continue

                block[target_index] = rewritten_target
                if definition_is_declaration and definition_variable.slot_scope is not None:
                    function.slot_scope_collector.remove_scope(
                        definition_variable.slot,
                        definition_variable.slot_scope,
                    )
                del block[i]
                inline_applied = True
                break

            if inline_applied:
                continue
            i += 1

    def _inline_numeric_for_start_temps(
        self, function: Function, block: list[Statement]
    ) -> None:
        def expression_use_count(
            expression: Optional[Expression],
            slot: int,
            target_scope: Optional[ScopeCell],
        ) -> int:
            if expression is None:
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
                variable = expression.variable
                if variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    if variable.slot != slot:
                        return 0
                    if target_scope is None:
                        return 1
                    return 1 if variable.slot_scope is target_scope else 0
                if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    return expression_use_count(
                        variable.table, slot, target_scope
                    ) + expression_use_count(variable.table_index, slot, target_scope)
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
                function_call = expression.function_call
                uses = expression_use_count(function_call.function, slot, target_scope)
                uses += expression_use_count(
                    function_call.multres_argument, slot, target_scope
                )
                for argument in function_call.arguments:
                    uses += expression_use_count(argument, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
                uses = expression_use_count(
                    expression.table.multres_field, slot, target_scope
                )
                for field in expression.table.fields:
                    uses += expression_use_count(field.key, slot, target_scope)
                    uses += expression_use_count(field.value, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
                return expression_use_count(
                    expression.binary_operation.left_operand, slot, target_scope
                ) + expression_use_count(
                    expression.binary_operation.right_operand, slot, target_scope
                )
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
                return expression_use_count(
                    expression.unary_operation.operand, slot, target_scope
                )
            return 0

        def statement_use_count(
            statement: Statement, slot: int, target_scope: Optional[ScopeCell]
        ) -> int:
            uses = expression_use_count(
                statement.assignment.multres_return, slot, target_scope
            )
            for expression in statement.assignment.expressions:
                uses += expression_use_count(expression, slot, target_scope)
            for variable in statement.assignment.variables:
                if variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    continue
                uses += expression_use_count(variable.table, slot, target_scope)
                uses += expression_use_count(variable.table_index, slot, target_scope)
            for nested in statement.block:
                uses += statement_use_count(nested, slot, target_scope)
            return uses

        def is_nil_or_empty_declaration(statement: Statement) -> bool:
            if statement.type != AST_STATEMENT.AST_STATEMENT_DECLARATION:
                return False
            if len(statement.assignment.variables) != 1:
                return False
            if not statement.assignment.expressions:
                return True
            return (
                len(statement.assignment.expressions) == 1
                and statement.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                and statement.assignment.expressions[-1].constant.type
                == AST_CONSTANT.AST_CONSTANT_NIL
            )

        for statement in block:
            if statement.block:
                self._inline_numeric_for_start_temps(function, statement.block)

        i = 1
        while i < len(block):
            current = block[i]
            if (
                current.type != AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR
                or len(current.assignment.expressions) < 2
                or current.assignment.expressions[0].type
                != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                or current.assignment.expressions[0].variable.type
                != AST_VARIABLE.AST_VARIABLE_SLOT
            ):
                i += 1
                continue

            start_variable = current.assignment.expressions[0].variable
            target_slot = start_variable.slot
            target_scope = start_variable.slot_scope

            prev = block[i - 1]
            replacement_expression: Optional[Expression] = None
            delete_from = i - 1
            delete_to = i

            if (
                prev.type in (
                    AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                    AST_STATEMENT.AST_STATEMENT_DECLARATION,
                )
                and len(prev.assignment.variables) == 1
                and len(prev.assignment.expressions) == 1
                and prev.assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                and prev.assignment.variables[-1].slot == target_slot
                and not function.is_valid_label(prev.instruction.label)
            ):
                replacement_expression = prev.assignment.expressions[-1]
            elif i >= 2:
                declaration = block[i - 2]
                assignment = block[i - 1]
                if (
                    is_nil_or_empty_declaration(declaration)
                    and len(declaration.assignment.variables) == 1
                    and declaration.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and declaration.assignment.variables[-1].slot == target_slot
                    and assignment.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(assignment.assignment.variables) == 1
                    and len(assignment.assignment.expressions) == 1
                    and assignment.assignment.variables[-1].type
                    == AST_VARIABLE.AST_VARIABLE_SLOT
                    and assignment.assignment.variables[-1].slot == target_slot
                    and not function.is_valid_label(declaration.instruction.label)
                    and not function.is_valid_label(assignment.instruction.label)
                ):
                    replacement_expression = assignment.assignment.expressions[-1]
                    delete_from = i - 2
                    delete_to = i

            if replacement_expression is None:
                i += 1
                continue

            use_count = 0
            for statement_index in range(i, len(block)):
                use_count += statement_use_count(
                    block[statement_index], target_slot, target_scope
                )
            if use_count != 1:
                i += 1
                continue

            current.assignment.expressions[0] = self._clone_expression_deep(
                replacement_expression
            )
            if target_scope is not None:
                function.slot_scope_collector.remove_scope(target_slot, target_scope)
            del block[delete_from:delete_to]
            i = max(delete_from, 1)

    def _remove_unused_empty_declarations(
        self, function: Function, block: list[Statement]
    ) -> None:
        def expression_use_count(
            expression: Optional[Expression],
            slot: int,
            target_scope: Optional[ScopeCell],
        ) -> int:
            if expression is None:
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
                variable = expression.variable
                if variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    if variable.slot != slot:
                        return 0
                    if target_scope is None:
                        return 1
                    return 1 if variable.slot_scope is target_scope else 0
                if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    return expression_use_count(
                        variable.table, slot, target_scope
                    ) + expression_use_count(variable.table_index, slot, target_scope)
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
                function_call = expression.function_call
                uses = expression_use_count(function_call.function, slot, target_scope)
                uses += expression_use_count(
                    function_call.multres_argument, slot, target_scope
                )
                for argument in function_call.arguments:
                    uses += expression_use_count(argument, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
                uses = expression_use_count(
                    expression.table.multres_field, slot, target_scope
                )
                for field in expression.table.fields:
                    uses += expression_use_count(field.key, slot, target_scope)
                    uses += expression_use_count(field.value, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
                return expression_use_count(
                    expression.binary_operation.left_operand, slot, target_scope
                ) + expression_use_count(
                    expression.binary_operation.right_operand, slot, target_scope
                )
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
                return expression_use_count(
                    expression.unary_operation.operand, slot, target_scope
                )
            return 0

        def statement_use_count(
            statement: Statement, slot: int, target_scope: Optional[ScopeCell]
        ) -> int:
            uses = expression_use_count(
                statement.assignment.multres_return, slot, target_scope
            )
            for expression in statement.assignment.expressions:
                uses += expression_use_count(expression, slot, target_scope)
            for variable in statement.assignment.variables:
                if variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    continue
                uses += expression_use_count(variable.table, slot, target_scope)
                uses += expression_use_count(variable.table_index, slot, target_scope)
            for nested in statement.block:
                uses += statement_use_count(nested, slot, target_scope)
            return uses

        for statement in block:
            if statement.block:
                self._remove_unused_empty_declarations(function, statement.block)

        i = 0
        while i < len(block):
            statement = block[i]
            if (
                statement.type == AST_STATEMENT.AST_STATEMENT_DECLARATION
                and len(statement.assignment.variables) == 1
                and statement.assignment.variables[-1].type
                == AST_VARIABLE.AST_VARIABLE_SLOT
                and (
                    not statement.assignment.expressions
                    or (
                        len(statement.assignment.expressions) == 1
                        and statement.assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                        and statement.assignment.expressions[-1].constant.type
                        == AST_CONSTANT.AST_CONSTANT_NIL
                    )
                )
                and not function.is_valid_label(statement.instruction.label)
            ):
                slot_variable = statement.assignment.variables[-1]
                slot_scope = slot_variable.slot_scope
                uses_after = 0
                for j in range(i + 1, len(block)):
                    uses_after += statement_use_count(block[j], slot_variable.slot, slot_scope)
                if uses_after == 0:
                    if slot_scope is not None:
                        function.slot_scope_collector.remove_scope(
                            slot_variable.slot, slot_scope
                        )
                    del block[i]
                    continue

            if (
                statement.type == AST_STATEMENT.AST_STATEMENT_DO
                and not statement.block
                and not function.is_valid_label(statement.instruction.label)
            ):
                del block[i]
                continue

            i += 1

    def build_if_statements_from_map(
        self,
        function: Function,
        block: list[Statement],
        previous_block: Optional[BlockInfo],
        offset_map: dict[Statement, int],
    ) -> None:
        block_info = BlockInfo(block=block, previous_block=previous_block)
        i = 0
        while i < len(block):
            if block[i].type == AST_STATEMENT.AST_STATEMENT_GOTO and block[i] not in offset_map:
                i += 1
                continue
            if block[i].type not in (
                AST_STATEMENT.AST_STATEMENT_GOTO,
                AST_STATEMENT.AST_STATEMENT_CONDITION,
            ):
                if block[i].type in (
                    AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR,
                    AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
                ):
                    self.build_if_statements(function, block[i].block, None)
                elif block[i].type in (
                    AST_STATEMENT.AST_STATEMENT_LOOP,
                    AST_STATEMENT.AST_STATEMENT_DECLARATION,
                ):
                    block_info.index = i
                    self.build_if_statements(function, block[i].block, block_info)
                i += 1
                continue

            function.remove_jump(block[i].instruction.id, block[i].instruction.target)
            index = offset_map[block[i]] + i

            if (
                block[i].type == AST_STATEMENT.AST_STATEMENT_GOTO
                and block[i].instruction.type == BC_OP.BC_OP_JMP
            ):
                block[i].type = AST_STATEMENT.AST_STATEMENT_EMPTY
                i += 1
                index += 1
                new_stmt = self.new_statement(AST_STATEMENT.AST_STATEMENT_GOTO)
                block.insert(i, new_stmt)
                block[i].instruction.id = block[i - 1].instruction.id
                block[i - 1].instruction.id = INVALID_ID

            block[i].block = list(block[i + 1 : index + 1])
            del block[i + 1 : index + 1]

            if (
                block[i].type == AST_STATEMENT.AST_STATEMENT_CONDITION
                and block[i].block
                and block[i].block[-1].type == AST_STATEMENT.AST_STATEMENT_GOTO
                and block[i].block[-1].instruction.type != BC_OP.BC_OP_LOOP
                and block[i].block[-1] in offset_map
            ):
                index = offset_map[block[i].block[-1]] + i
                else_stmt = self.new_statement(AST_STATEMENT.AST_STATEMENT_ELSE)
                block.insert(i + 1, else_stmt)
                block[i + 1].block = list(block[i + 2 : index + 2])
                del block[i + 2 : index + 2]
                function.remove_jump(
                    block[i].block[-1].instruction.id, block[i].block[-1].instruction.target
                )
                block[i].block[-1].type = AST_STATEMENT.AST_STATEMENT_EMPTY
                block_info.index = i + 1
                self.build_if_statements_from_map(
                    function, block[i + 1].block, block_info, offset_map
                )

            if block[i].type == AST_STATEMENT.AST_STATEMENT_GOTO:
                block[i].assignment.expressions.append(self.new_primitive(1))
            block[i].type = AST_STATEMENT.AST_STATEMENT_IF
            block_info.index = i
            self.build_if_statements_from_map(function, block[i].block, block_info, offset_map)
            i += 1

    def build_if_statements(
        self,
        function: Function,
        block: list[Statement],
        previous_block: Optional[BlockInfo],
    ) -> None:
        def build_if_false_statements(
            current_block: list[Statement], parent_block: Optional[BlockInfo]
        ) -> None:
            block_info = BlockInfo(block=current_block, previous_block=parent_block)
            i = len(current_block) - 1
            while i >= 0:
                if (
                    current_block[i].type != AST_STATEMENT.AST_STATEMENT_GOTO
                    or current_block[i].instruction.type == BC_OP.BC_OP_LOOP
                ):
                    i -= 1
                    continue
                target_label = INVALID_ID
                index = i
                while index < len(current_block):
                    block_info.index = index
                    target_label = Ast.get_label_from_next_statement(
                        function, block_info, False, False
                    )
                    if (
                        target_label == INVALID_ID
                        or function.labels[target_label].target
                        != current_block[i].instruction.target
                    ):
                        target_label = Ast.get_label_from_next_statement(
                            function, block_info, True, False
                        )
                    if target_label == INVALID_ID:
                        index += 1
                        continue
                    if (
                        function.labels[target_label].target == current_block[i].instruction.target
                        and Ast.is_valid_block(
                            function, block_info, current_block[i].instruction.id + 1
                        )
                    ):
                        break
                    target_label = INVALID_ID
                    index += 1

                if target_label == INVALID_ID:
                    i -= 1
                    continue

                function.remove_jump(
                    current_block[i].instruction.id, current_block[i].instruction.target
                )
                if current_block[i].instruction.type == BC_OP.BC_OP_JMP:
                    current_block[i].type = AST_STATEMENT.AST_STATEMENT_EMPTY
                    i += 1
                    index += 1
                    if_stmt = self.new_statement(AST_STATEMENT.AST_STATEMENT_IF)
                    current_block.insert(i, if_stmt)
                    current_block[i].instruction.id = current_block[i - 1].instruction.id
                    current_block[i - 1].instruction.id = INVALID_ID
                else:
                    current_block[i].type = AST_STATEMENT.AST_STATEMENT_IF

                current_block[i].assignment.expressions.append(self.new_primitive(1))
                current_block[i].block = list(current_block[i + 1 : index + 1])
                del current_block[i + 1 : index + 1]
                i -= 1

        def build_else_statements(
            current_block: list[Statement], parent_block: Optional[BlockInfo]
        ) -> None:
            block_info = BlockInfo(block=current_block, previous_block=parent_block)
            i = len(current_block) - 1
            while i >= 0:
                if current_block[i].type != AST_STATEMENT.AST_STATEMENT_IF:
                    i -= 1
                    continue

                if (
                    current_block[i].block
                    and current_block[i].block[-1].type == AST_STATEMENT.AST_STATEMENT_GOTO
                    and current_block[i].block[-1].instruction.type != BC_OP.BC_OP_LOOP
                ):
                    target_label = INVALID_ID
                    index = i
                    while index < len(current_block):
                        block_info.index = index
                        target_label = Ast.get_label_from_next_statement(
                            function, block_info, False, False
                        )
                        if (
                            target_label == INVALID_ID
                            or function.labels[target_label].target
                            != current_block[i].block[-1].instruction.target
                        ):
                            target_label = Ast.get_label_from_next_statement(
                                function, block_info, True, False
                            )
                        if target_label == INVALID_ID:
                            index += 1
                            continue
                        if (
                            function.labels[target_label].target
                            == current_block[i].block[-1].instruction.target
                            and Ast.is_valid_block(
                                function, block_info, current_block[i].block[-1].instruction.id + 1
                            )
                        ):
                            break
                        target_label = INVALID_ID
                        index += 1

                    if target_label != INVALID_ID:
                        else_stmt = self.new_statement(AST_STATEMENT.AST_STATEMENT_ELSE)
                        current_block.insert(i + 1, else_stmt)
                        current_block[i + 1].block = list(current_block[i + 2 : index + 2])
                        del current_block[i + 2 : index + 2]
                        function.remove_jump(
                            current_block[i].block[-1].instruction.id,
                            current_block[i].block[-1].instruction.target,
                        )
                        current_block[i].block[-1].type = AST_STATEMENT.AST_STATEMENT_EMPTY
                        block_info.index = i + 1
                        build_if_false_statements(current_block[i + 1].block, block_info)
                        build_if_false_statements(current_block[i].block, None)
                        i -= 1
                        continue

                block_info.index = i
                build_if_false_statements(current_block[i].block, block_info)
                i -= 1

        block_info = BlockInfo(block=block, previous_block=previous_block)
        indexes: list[int] = []
        offset_map: dict[Statement, int] = {}
        i = 0
        while i < len(block):
            if indexes and (i == indexes[-1] or block[i].type != AST_STATEMENT.AST_STATEMENT_CONDITION):
                block_info.index = i
                target_label = Ast.get_label_from_next_statement(function, block_info, False, False)
                if (
                    target_label == INVALID_ID
                    or function.labels[target_label].target != block[indexes[-1]].instruction.target
                ):
                    target_label = Ast.get_label_from_next_statement(
                        function, block_info, True, False
                    )

                if (
                    target_label != INVALID_ID
                    and function.labels[target_label].target == block[indexes[-1]].instruction.target
                    and Ast.is_valid_block(
                        function,
                        block_info,
                        block[indexes[-1]].instruction.id
                        + (2 if block[indexes[-1]].type == AST_STATEMENT.AST_STATEMENT_CONDITION else 1),
                    )
                ):
                    offset_map[block[indexes[-1]]] = i - indexes[-1]
                    if (
                        i - indexes[-1]
                        and block[indexes[-1]].type == AST_STATEMENT.AST_STATEMENT_CONDITION
                        and block[i].type == AST_STATEMENT.AST_STATEMENT_GOTO
                        and block[i].instruction.type != BC_OP.BC_OP_LOOP
                    ):
                        function.remove_jump(
                            block[indexes[-1]].instruction.id,
                            block[indexes[-1]].instruction.target,
                        )
                        indexes.append(i)
                        i -= 1
                        i += 1
                        continue

                    if len(indexes) >= 2 and block[indexes[-2]] in offset_map:
                        indexes.pop()
                        function.add_jump(
                            block[indexes[-1]].instruction.id,
                            block[indexes[-1]].instruction.target,
                        )

                    indexes.pop()
                    i -= 1
                    i += 1
                    continue

                if i == indexes[-1]:
                    i += 1
                    continue

            if block[i].type in (
                AST_STATEMENT.AST_STATEMENT_GOTO,
                AST_STATEMENT.AST_STATEMENT_CONDITION,
            ):
                if (
                    block[i].type == AST_STATEMENT.AST_STATEMENT_GOTO
                    and block[i].instruction.type == BC_OP.BC_OP_LOOP
                ):
                    i += 1
                    continue
                if block[i] in offset_map:
                    i += 1
                    continue
                indexes.append(i)
                i -= 1
            i += 1

        if (
            len(indexes) == 1
            and block[indexes[-1]].type == AST_STATEMENT.AST_STATEMENT_GOTO
            and indexes[-1] == len(block) - 1
            and previous_block is not None
            and previous_block.block[previous_block.index].type == AST_STATEMENT.AST_STATEMENT_LOOP
        ):
            indexes.pop()

        if not indexes:
            self.build_if_statements_from_map(function, block, previous_block, offset_map)
            return

        for j in range(len(indexes) - 1, -1, -1):
            if block[indexes[j]] in offset_map:
                function.add_jump(block[indexes[j]].instruction.id, block[indexes[j]].instruction.target)

        i = len(block) - 1
        while i >= 0:
            if block[i].type == AST_STATEMENT.AST_STATEMENT_CONDITION:
                block[i].type = AST_STATEMENT.AST_STATEMENT_IF
                target_label = INVALID_ID
                index = i
                while index < len(block):
                    block_info.index = index
                    target_label = Ast.get_label_from_next_statement(
                        function, block_info, False, False
                    )
                    if (
                        target_label == INVALID_ID
                        or function.labels[target_label].target != block[i].instruction.target
                    ):
                        target_label = Ast.get_label_from_next_statement(
                            function, block_info, True, False
                        )
                    if target_label == INVALID_ID:
                        index += 1
                        continue
                    if (
                        function.labels[target_label].target == block[i].instruction.target
                        and Ast.is_valid_block(function, block_info, block[i].instruction.id + 2)
                    ):
                        break
                    target_label = INVALID_ID
                    index += 1

                failure_message = (
                    "Failed to build if statement "
                    f"(function_id={function.id}, level={function.level}, "
                    f"statement_index={i}, instruction_id={block[i].instruction.id}, "
                    f"target_id={block[i].instruction.target})"
                )
                if target_label == INVALID_ID:
                    snapshot_parts: list[str] = []
                    for snapshot_index, snapshot_statement in enumerate(block):
                        snapshot_parts.append(
                            (
                                f"{snapshot_index}:"
                                f"{snapshot_statement.type.name}"
                                f"/op={snapshot_statement.instruction.type.name if snapshot_statement.instruction.type is not None else 'NONE'}"
                                f"/id={snapshot_statement.instruction.id}"
                                f"/target={snapshot_statement.instruction.target}"
                                f"/label={snapshot_statement.instruction.label}"
                            )
                        )
                    label_parts: list[str] = []
                    for label_index, label in enumerate(function.labels):
                        label_parts.append(
                            f"{label_index}:target={label.target},jumps={label.jump_ids}"
                        )
                    failure_message += " | block_snapshot=[" + "; ".join(snapshot_parts) + "]"
                    failure_message += " | labels=[" + "; ".join(label_parts) + "]"

                decompiler_assert(
                    target_label != INVALID_ID,
                    failure_message,
                    self.bytecode.file_path,
                    "Ast::build_if_statements",
                    __file__,
                    0,
                )
                block[i].block = list(block[i + 1 : index + 1])
                del block[i + 1 : index + 1]
                function.remove_jump(block[i].instruction.id, block[i].instruction.target)
                block_info.index = i
                build_else_statements(block[i].block, block_info)
            elif block[i].type in (
                AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR,
                AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
            ):
                self.build_if_statements(function, block[i].block, None)
            elif block[i].type in (
                AST_STATEMENT.AST_STATEMENT_LOOP,
                AST_STATEMENT.AST_STATEMENT_DECLARATION,
            ):
                block_info.index = i
                self.build_if_statements(function, block[i].block, block_info)
            i -= 1

        build_else_statements(block, previous_block)
        build_if_false_statements(block, previous_block)

    def clean_up(self, function: Function) -> None:
        if function.has_debug_info:
            for i in range(len(function.parameter_names) - 1, -1, -1):
                cell = function.slot_scope_collector.slot_infos[i].active_slot_scope
                if cell is not None:
                    cell.scope.name = function.parameter_names[i]
        else:
            function.parameter_names = [""] * function.prototype.header.parameters
            for i in range(len(function.parameter_names) - 1, -1, -1):
                function.parameter_names[i] = self._format_arg_name(function, i)
                cell = function.slot_scope_collector.slot_infos[i].active_slot_scope
                if cell is not None:
                    cell.scope.name = function.parameter_names[i]

        variable_counter = 0
        iterator_counter = 0
        variable_counter, iterator_counter = self.clean_up_block(
            function, function.block, variable_counter, iterator_counter, None
        )

        label_counter = 0
        for i in range(len(function.labels)):
            if not function.labels[i].jump_ids:
                continue
            function.labels[i].name = self._format_label_name(function, label_counter)
            label_counter += 1

    @staticmethod
    def _is_slot_or_upvalue_variable_expression(expression: Optional[Expression]) -> bool:
        return (
            expression is not None
            and expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
            and expression.variable.type
            in (AST_VARIABLE.AST_VARIABLE_SLOT, AST_VARIABLE.AST_VARIABLE_UPVALUE)
            and expression.variable.slot_scope is not None
        )

    @staticmethod
    def _extract_string_key(field_key: Optional[Expression]) -> Optional[str]:
        if (
            field_key is None
            or field_key.type != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
            or field_key.constant.type != AST_CONSTANT.AST_CONSTANT_STRING
        ):
            return None
        return field_key.constant.string

    @staticmethod
    def _extract_positive_integer_key(field_key: Optional[Expression]) -> Optional[int]:
        if (
            field_key is None
            or field_key.type != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
            or field_key.constant.type != AST_CONSTANT.AST_CONSTANT_NUMBER
        ):
            return None
        number = field_key.constant.number
        if number <= 0 or int(number) != number:
            return None
        return int(number)

    @staticmethod
    def _is_dup_key(key: str) -> bool:
        if not key.startswith("dup") or len(key) <= 3:
            return False
        return key[3:].isdigit()

    def _clone_table_field(self, field: AstTableField) -> AstTableField:
        return AstTableField(
            key=self._clone_expression_shallow(field.key) if field.key is not None else None,
            value=self._clone_expression_shallow(field.value) if field.value is not None else None,
        )

    def _clone_expression_deep(self, expression: Optional[Expression]) -> Optional[Expression]:
        if expression is None:
            return None

        clone = self.new_expression(expression.type)

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT:
            clone.constant = AstConstant(
                type=expression.constant.type,
                number=expression.constant.number,
                signed_integer=expression.constant.signed_integer,
                unsigned_integer=expression.constant.unsigned_integer,
                string=expression.constant.string,
                is_name=expression.constant.is_name,
            )
            return clone

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARARG:
            clone.return_count = expression.return_count
            return clone

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION:
            clone.function = expression.function
            return clone

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
            variable = expression.variable
            clone.variable = AstVariable(
                type=variable.type,
                slot=variable.slot,
                slot_scope=variable.slot_scope,
                name=variable.name,
                table=self._clone_expression_deep(variable.table),
                table_index=self._clone_expression_deep(variable.table_index),
                is_multres=variable.is_multres,
                multres_index=variable.multres_index,
            )
            return clone

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
            clone.function_call = AstFunctionCall(
                function=self._clone_expression_deep(expression.function_call.function),
                arguments=[
                    self._clone_expression_deep(argument)
                    for argument in expression.function_call.arguments
                ],
                multres_argument=self._clone_expression_deep(
                    expression.function_call.multres_argument
                ),
                is_method=expression.function_call.is_method,
                return_count=expression.function_call.return_count,
            )
            return clone

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
            clone.table = AstTable(
                constants=AstTableConstants(
                    list=[
                        self._clone_expression_deep(value)
                        for value in expression.table.constants.list
                    ],
                    fields=[
                        AstTableField(
                            key=self._clone_expression_deep(field.key),
                            value=self._clone_expression_deep(field.value),
                        )
                        for field in expression.table.constants.fields
                    ],
                ),
                fields=[
                    AstTableField(
                        key=self._clone_expression_deep(field.key),
                        value=self._clone_expression_deep(field.value),
                    )
                    for field in expression.table.fields
                ],
                multres_index=expression.table.multres_index,
                multres_field=self._clone_expression_deep(expression.table.multres_field),
            )
            return clone

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            clone.binary_operation = AstBinaryOperation(
                type=expression.binary_operation.type,
                left_operand=self._clone_expression_deep(
                    expression.binary_operation.left_operand
                ),
                right_operand=self._clone_expression_deep(
                    expression.binary_operation.right_operand
                ),
            )
            return clone

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            clone.unary_operation = AstUnaryOperation(
                type=expression.unary_operation.type,
                operand=self._clone_expression_deep(expression.unary_operation.operand),
            )
            return clone

        return clone

    @staticmethod
    def _statement_single_table_assignment(
        statement: Statement,
    ) -> tuple[Optional[AstVariable], Optional[Expression]]:
        if statement.type not in (
            AST_STATEMENT.AST_STATEMENT_DECLARATION,
            AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
        ):
            return None, None
        if (
            len(statement.assignment.variables) != 1
            or len(statement.assignment.expressions) != 1
            or statement.assignment.expressions[0].type != AST_EXPRESSION.AST_EXPRESSION_TABLE
        ):
            return None, None
        return statement.assignment.variables[0], statement.assignment.expressions[0]

    def _find_table_initializer_before(
        self, block: list[Statement], scope: ScopeCell, end_index: int
    ) -> tuple[Optional[int], Optional[Expression]]:
        for i in range(end_index - 1, -1, -1):
            variable, expression = self._statement_single_table_assignment(block[i])
            if variable is None or expression is None:
                continue
            if (
                variable.type == AST_VARIABLE.AST_VARIABLE_SLOT
                and variable.slot_scope is scope
            ):
                return i, expression
        return None, None

    def _extract_meta_index_function(self, metatable_expression: Expression) -> Optional[Function]:
        if metatable_expression.type != AST_EXPRESSION.AST_EXPRESSION_TABLE:
            return None
        table = metatable_expression.table
        for field in table.fields:
            if self._extract_string_key(field.key) != "__index":
                continue
            if field.value is None or field.value.type != AST_EXPRESSION.AST_EXPRESSION_FUNCTION:
                continue
            return field.value.function
        return None

    def _extract_default_table_scope_from_index(self, index_function: Function) -> Optional[ScopeCell]:
        for i in range(len(index_function.block) - 1):
            statement = index_function.block[i]
            if statement.type not in (
                AST_STATEMENT.AST_STATEMENT_DECLARATION,
                AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
            ):
                continue
            if len(statement.assignment.variables) != 1 or len(statement.assignment.expressions) != 1:
                continue

            local_variable = statement.assignment.variables[0]
            local_scope = local_variable.slot_scope
            expression = statement.assignment.expressions[0]
            if (
                local_scope is None
                or expression.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                or expression.variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                or not self._is_slot_or_upvalue_variable_expression(expression.variable.table)
            ):
                continue

            next_statement = index_function.block[i + 1]
            if (
                next_statement.type != AST_STATEMENT.AST_STATEMENT_IF
                or len(next_statement.assignment.expressions) != 1
                or next_statement.assignment.expressions[0].type
                != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                or next_statement.assignment.expressions[0].variable.type
                != AST_VARIABLE.AST_VARIABLE_SLOT
                or next_statement.assignment.expressions[0].variable.slot_scope is not local_scope
                or not next_statement.block
                or next_statement.block[0].type != AST_STATEMENT.AST_STATEMENT_RETURN
                or len(next_statement.block[0].assignment.expressions) != 1
                or next_statement.block[0].assignment.expressions[0].type
                != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                or next_statement.block[0].assignment.expressions[0].variable.type
                != AST_VARIABLE.AST_VARIABLE_SLOT
                or next_statement.block[0].assignment.expressions[0].variable.slot_scope
                is not local_scope
            ):
                continue

            table_variable = expression.variable.table.variable
            return table_variable.slot_scope

        return None

    def _extract_pairs_argument_scope(self, generic_for_statement: Statement) -> Optional[ScopeCell]:
        if (
            generic_for_statement.type != AST_STATEMENT.AST_STATEMENT_GENERIC_FOR
            or len(generic_for_statement.assignment.expressions) != 1
        ):
            return None
        expression = generic_for_statement.assignment.expressions[0]
        if (
            expression.type != AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
            or expression.function_call.function is None
            or expression.function_call.function.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
            or expression.function_call.function.variable.type != AST_VARIABLE.AST_VARIABLE_GLOBAL
            or expression.function_call.function.variable.name != "pairs"
            or len(expression.function_call.arguments) != 1
            or not self._is_slot_or_upvalue_variable_expression(expression.function_call.arguments[0])
        ):
            return None
        return expression.function_call.arguments[0].variable.slot_scope

    def _extract_metatable_scope_from_setmetatable_loop(
        self, generic_for_statement: Statement
    ) -> Optional[ScopeCell]:
        if (
            generic_for_statement.type != AST_STATEMENT.AST_STATEMENT_GENERIC_FOR
            or len(generic_for_statement.assignment.variables) < 2
            or len(generic_for_statement.block) != 1
        ):
            return None

        body_statement = generic_for_statement.block[0]
        if (
            body_statement.type != AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL
            or len(body_statement.assignment.expressions) != 1
            or body_statement.assignment.expressions[0].type
            != AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
        ):
            return None

        function_call = body_statement.assignment.expressions[0].function_call
        if (
            function_call.function is None
            or function_call.function.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
            or function_call.function.variable.type != AST_VARIABLE.AST_VARIABLE_GLOBAL
            or function_call.function.variable.name != "setmetatable"
            or len(function_call.arguments) != 2
            or not self._is_slot_or_upvalue_variable_expression(function_call.arguments[0])
            or not self._is_slot_or_upvalue_variable_expression(function_call.arguments[1])
        ):
            return None

        loop_value_scope = generic_for_statement.assignment.variables[-1].slot_scope
        if loop_value_scope is None or function_call.arguments[0].variable.slot_scope is not loop_value_scope:
            return None

        return function_call.arguments[1].variable.slot_scope

    def _decompress_table_rows(
        self, data_table_expression: Expression, default_table_expression: Expression
    ) -> bool:
        if (
            data_table_expression.type != AST_EXPRESSION.AST_EXPRESSION_TABLE
            or default_table_expression.type != AST_EXPRESSION.AST_EXPRESSION_TABLE
        ):
            return False

        default_fields: list[AstTableField] = []
        default_fields.extend(default_table_expression.table.constants.fields)
        default_fields.extend(default_table_expression.table.fields)
        default_fields = [
            field
            for field in default_fields
            if field.key is not None
            and field.value is not None
            and self._extract_string_key(field.key) is not None
        ]
        if not default_fields:
            return False

        row_tables: list[AstTable] = []
        for value in data_table_expression.table.constants.list:
            if value.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
                row_tables.append(value.table)
        for field in data_table_expression.table.constants.fields:
            if (
                self._extract_positive_integer_key(field.key) is not None
                and field.value is not None
                and field.value.type == AST_EXPRESSION.AST_EXPRESSION_TABLE
            ):
                row_tables.append(field.value.table)
        for field in data_table_expression.table.fields:
            if (
                self._extract_positive_integer_key(field.key) is not None
                and field.value is not None
                and field.value.type == AST_EXPRESSION.AST_EXPRESSION_TABLE
            ):
                row_tables.append(field.value.table)
        if not row_tables:
            return False

        changed = False
        for row_table in row_tables:
            row_fields: list[AstTableField] = []
            row_fields.extend(row_table.constants.fields)
            row_fields.extend(row_table.fields)

            for default_field in default_fields:
                exists = False
                for row_field in row_fields:
                    if Ast._expressions_equivalent(row_field.key, default_field.key):
                        exists = True
                        break

                if exists:
                    continue

                row_table.constants.fields.append(self._clone_table_field(default_field))
                changed = True

        return changed

    def _extract_dup_pool_map(self, table_expression: Expression) -> Optional[dict[str, Expression]]:
        if table_expression.type != AST_EXPRESSION.AST_EXPRESSION_TABLE:
            return None

        dup_map: dict[str, Expression] = {}
        for field in table_expression.table.constants.fields:
            key = self._extract_string_key(field.key)
            if key is None or not self._is_dup_key(key) or field.value is None:
                continue
            dup_map[key] = field.value

        for field in table_expression.table.fields:
            key = self._extract_string_key(field.key)
            if key is None or not self._is_dup_key(key) or field.value is None:
                continue
            dup_map[key] = field.value

        if not dup_map:
            return None

        return dup_map

    def _inline_dup_pool_refs_in_expression(
        self,
        expression: Optional[Expression],
        pools: list[tuple[ScopeCell, dict[str, Expression]]],
    ) -> int:
        if expression is None:
            return 0

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
            variable = expression.variable

            if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                key = self._extract_string_key(variable.table_index)
                if (
                    key is not None
                    and self._is_slot_or_upvalue_variable_expression(variable.table)
                ):
                    table_scope = variable.table.variable.slot_scope
                    for pool_scope, pool_map in reversed(pools):
                        if pool_scope is not table_scope or key not in pool_map:
                            continue
                        replacement = self._clone_expression_deep(pool_map[key])
                        if replacement is not None:
                            expression.assign_from(replacement)
                            return 1
                        break

                replaced = 0
                replaced += self._inline_dup_pool_refs_in_expression(variable.table, pools)
                replaced += self._inline_dup_pool_refs_in_expression(variable.table_index, pools)
                return replaced

            return 0

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
            replaced = self._inline_dup_pool_refs_in_expression(
                expression.function_call.function, pools
            )
            for argument in expression.function_call.arguments:
                replaced += self._inline_dup_pool_refs_in_expression(argument, pools)
            replaced += self._inline_dup_pool_refs_in_expression(
                expression.function_call.multres_argument, pools
            )
            return replaced

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
            replaced = 0
            for value in expression.table.constants.list:
                replaced += self._inline_dup_pool_refs_in_expression(value, pools)
            for field in expression.table.constants.fields:
                replaced += self._inline_dup_pool_refs_in_expression(field.key, pools)
                replaced += self._inline_dup_pool_refs_in_expression(field.value, pools)
            for field in expression.table.fields:
                replaced += self._inline_dup_pool_refs_in_expression(field.key, pools)
                replaced += self._inline_dup_pool_refs_in_expression(field.value, pools)
            replaced += self._inline_dup_pool_refs_in_expression(
                expression.table.multres_field, pools
            )
            return replaced

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            replaced = self._inline_dup_pool_refs_in_expression(
                expression.binary_operation.left_operand, pools
            )
            replaced += self._inline_dup_pool_refs_in_expression(
                expression.binary_operation.right_operand, pools
            )
            return replaced

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            return self._inline_dup_pool_refs_in_expression(
                expression.unary_operation.operand, pools
            )

        return 0

    def _inline_dup_pool_refs_in_statement(
        self,
        statement: Statement,
        pools: list[tuple[ScopeCell, dict[str, Expression]]],
    ) -> int:
        replaced = 0

        for expression in statement.assignment.expressions:
            replaced += self._inline_dup_pool_refs_in_expression(expression, pools)
        replaced += self._inline_dup_pool_refs_in_expression(
            statement.assignment.multres_return, pools
        )

        for variable in statement.assignment.variables:
            if variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                continue
            replaced += self._inline_dup_pool_refs_in_expression(variable.table, pools)
            replaced += self._inline_dup_pool_refs_in_expression(variable.table_index, pools)

        if statement.block:
            replaced += self._inline_dup_pool_refs_in_block(statement.block, pools)

        return replaced

    def _inline_dup_pool_refs_in_block(
        self,
        block: list[Statement],
        inherited_pools: Optional[list[tuple[ScopeCell, dict[str, Expression]]]] = None,
    ) -> int:
        pools: list[tuple[ScopeCell, dict[str, Expression]]] = (
            list(inherited_pools) if inherited_pools is not None else []
        )
        replaced = 0

        for statement in block:
            replaced += self._inline_dup_pool_refs_in_statement(statement, pools)

            variable, table_expression = self._statement_single_table_assignment(statement)
            if (
                variable is None
                or table_expression is None
                or variable.type not in (AST_VARIABLE.AST_VARIABLE_SLOT, AST_VARIABLE.AST_VARIABLE_UPVALUE)
                or variable.slot_scope is None
            ):
                continue

            dup_map = self._extract_dup_pool_map(table_expression)
            if dup_map is None:
                continue
            pools.append((variable.slot_scope, dup_map))

        return replaced

    def _is_metatable_protection_assignment(
        self, statement: Statement, metatable_scope: ScopeCell
    ) -> bool:
        if (
            statement.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
            or len(statement.assignment.variables) != 1
        ):
            return False
        variable = statement.assignment.variables[0]
        if (
            variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
            or not self._is_slot_or_upvalue_variable_expression(variable.table)
            or variable.table.variable.slot_scope is not metatable_scope
        ):
            return False
        key = self._extract_string_key(variable.table_index)
        return key == "__metatable"

    def _expression_is_side_effect_free(self, expression: Optional[Expression]) -> bool:
        if expression is None:
            return True

        if expression.type in (
            AST_EXPRESSION.AST_EXPRESSION_CONSTANT,
            AST_EXPRESSION.AST_EXPRESSION_VARIABLE,
            AST_EXPRESSION.AST_EXPRESSION_VARARG,
            AST_EXPRESSION.AST_EXPRESSION_FUNCTION,
        ):
            return True

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
            return False

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
            table = expression.table
            if table.multres_field is not None:
                return False
            for value in table.constants.list:
                if not self._expression_is_side_effect_free(value):
                    return False
            for field in table.constants.fields:
                if not self._expression_is_side_effect_free(
                    field.key
                ) or not self._expression_is_side_effect_free(field.value):
                    return False
            for field in table.fields:
                if not self._expression_is_side_effect_free(
                    field.key
                ) or not self._expression_is_side_effect_free(field.value):
                    return False
            return True

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            return self._expression_is_side_effect_free(
                expression.binary_operation.left_operand
            ) and self._expression_is_side_effect_free(expression.binary_operation.right_operand)

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            return self._expression_is_side_effect_free(expression.unary_operation.operand)

        return False

    def _collect_used_slot_scopes_in_expression(
        self, expression: Optional[Expression], used_scopes: set[ScopeCell]
    ) -> None:
        if expression is None:
            return

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
            variable = expression.variable
            if variable.type in (
                AST_VARIABLE.AST_VARIABLE_SLOT,
                AST_VARIABLE.AST_VARIABLE_UPVALUE,
            ):
                if variable.slot_scope is not None:
                    used_scopes.add(variable.slot_scope)
                return

            if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                self._collect_used_slot_scopes_in_expression(variable.table, used_scopes)
                self._collect_used_slot_scopes_in_expression(variable.table_index, used_scopes)
            return

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION:
            if expression.function is None:
                return
            for upvalue in expression.function.upvalues:
                if upvalue.slot_scope is not None:
                    used_scopes.add(upvalue.slot_scope)
            return

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
            self._collect_used_slot_scopes_in_expression(
                expression.function_call.function, used_scopes
            )
            for argument in expression.function_call.arguments:
                self._collect_used_slot_scopes_in_expression(argument, used_scopes)
            self._collect_used_slot_scopes_in_expression(
                expression.function_call.multres_argument, used_scopes
            )
            return

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
            for value in expression.table.constants.list:
                self._collect_used_slot_scopes_in_expression(value, used_scopes)
            for field in expression.table.constants.fields:
                self._collect_used_slot_scopes_in_expression(field.key, used_scopes)
                self._collect_used_slot_scopes_in_expression(field.value, used_scopes)
            for field in expression.table.fields:
                self._collect_used_slot_scopes_in_expression(field.key, used_scopes)
                self._collect_used_slot_scopes_in_expression(field.value, used_scopes)
            self._collect_used_slot_scopes_in_expression(
                expression.table.multres_field, used_scopes
            )
            return

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            self._collect_used_slot_scopes_in_expression(
                expression.binary_operation.left_operand, used_scopes
            )
            self._collect_used_slot_scopes_in_expression(
                expression.binary_operation.right_operand, used_scopes
            )
            return

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            self._collect_used_slot_scopes_in_expression(
                expression.unary_operation.operand, used_scopes
            )

    def _collect_used_slot_scopes_in_statement(
        self, statement: Statement, used_scopes: set[ScopeCell]
    ) -> None:
        for expression in statement.assignment.expressions:
            self._collect_used_slot_scopes_in_expression(expression, used_scopes)
        self._collect_used_slot_scopes_in_expression(
            statement.assignment.multres_return, used_scopes
        )

        for variable in statement.assignment.variables:
            if variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                continue
            self._collect_used_slot_scopes_in_expression(variable.table, used_scopes)
            self._collect_used_slot_scopes_in_expression(variable.table_index, used_scopes)

        for child_statement in statement.block:
            self._collect_used_slot_scopes_in_statement(child_statement, used_scopes)

    def _prune_unused_local_initializers(self, block: list[Statement]) -> None:
        while True:
            used_scopes: set[ScopeCell] = set()
            for statement in block:
                self._collect_used_slot_scopes_in_statement(statement, used_scopes)

            changed = False
            i = len(block) - 1
            while i >= 0:
                statement = block[i]

                if statement.type not in (
                    AST_STATEMENT.AST_STATEMENT_DECLARATION,
                    AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
                ):
                    i -= 1
                    continue

                if (
                    len(statement.assignment.variables) != 1
                    or statement.assignment.variables[0].type != AST_VARIABLE.AST_VARIABLE_SLOT
                    or statement.assignment.variables[0].slot_scope is None
                    or statement.assignment.variables[0].slot_scope in used_scopes
                    or len(statement.assignment.expressions) != 1
                    or not self._expression_is_side_effect_free(
                        statement.assignment.expressions[0]
                    )
                ):
                    i -= 1
                    continue

                del block[i]
                changed = True
                i -= 1

            if not changed:
                break

    def _decompress_tables_in_block(
        self, block: list[Statement], aggressive: bool
    ) -> None:
        for statement in block:
            if statement.block:
                self._decompress_tables_in_block(statement.block, aggressive)

        i = 0
        remove_indices: set[int] = set()
        while i < len(block):
            statement = block[i]
            if statement.type != AST_STATEMENT.AST_STATEMENT_GENERIC_FOR:
                i += 1
                continue

            data_table_scope = self._extract_pairs_argument_scope(statement)
            metatable_scope = self._extract_metatable_scope_from_setmetatable_loop(statement)
            if data_table_scope is None or metatable_scope is None:
                i += 1
                continue

            metatable_index, metatable_expression = self._find_table_initializer_before(
                block, metatable_scope, i
            )
            if metatable_expression is None:
                i += 1
                continue

            index_function = self._extract_meta_index_function(metatable_expression)
            if index_function is None:
                i += 1
                continue

            default_table_scope = self._extract_default_table_scope_from_index(index_function)
            if default_table_scope is None:
                i += 1
                continue

            _, data_table_expression = self._find_table_initializer_before(
                block, data_table_scope, i
            )
            if data_table_expression is None:
                i += 1
                continue

            _, default_table_expression = self._find_table_initializer_before(
                block, default_table_scope, metatable_index if metatable_index is not None else i
            )
            if default_table_expression is None:
                i += 1
                continue

            self._decompress_table_rows(data_table_expression, default_table_expression)
            if aggressive:
                remove_indices.add(i)
                for j in range(i + 1, len(block)):
                    if self._is_metatable_protection_assignment(block[j], metatable_scope):
                        remove_indices.add(j)
                        break
            i += 1

        if aggressive and remove_indices:
            for index in sorted(remove_indices, reverse=True):
                del block[index]
            self._prune_unused_local_initializers(block)

    def decompress_tables(self, aggressive: bool = False) -> None:
        if self.chunk is None:
            return
        self._decompress_tables_in_block(self.chunk.block, aggressive)
        self._inline_dup_pool_refs_in_block(self.chunk.block, None)
        if aggressive:
            self._prune_unused_local_initializers(self.chunk.block)

    def clean_up_block(
        self,
        function: Function,
        block: list[Statement],
        variable_counter: int,
        iterator_counter: int,
        previous_block: Optional[BlockInfo],
    ) -> tuple[int, int]:
        block_info = BlockInfo(block=block, previous_block=previous_block)
        variable_counter, iterator_counter = self._cleanup_pass1(
            function, block, variable_counter, iterator_counter, block_info
        )
        self._cleanup_insert_labels(function, block)
        self._cleanup_finalize_declarations(function, block)
        return variable_counter, iterator_counter

    @staticmethod
    def _expressions_equivalent(a: Optional[Expression], b: Optional[Expression]) -> bool:
        if a is None or b is None:
            return a is b
        if a.type != b.type:
            return False

        if a.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT:
            ca = a.constant
            cb = b.constant
            if ca.type != cb.type:
                return False
            if ca.type == AST_CONSTANT.AST_CONSTANT_NUMBER:
                return ca.number == cb.number
            if ca.type == AST_CONSTANT.AST_CONSTANT_STRING:
                return ca.string == cb.string
            if ca.type == AST_CONSTANT.AST_CONSTANT_CDATA_SIGNED:
                return ca.signed_integer == cb.signed_integer
            if ca.type == AST_CONSTANT.AST_CONSTANT_CDATA_UNSIGNED:
                return ca.unsigned_integer == cb.unsigned_integer
            if ca.type == AST_CONSTANT.AST_CONSTANT_CDATA_IMAGINARY:
                return ca.number == cb.number
            return True

        if a.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
            va = a.variable
            vb = b.variable
            if va.type != vb.type:
                return False
            if va.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                return va.slot == vb.slot
            if va.type == AST_VARIABLE.AST_VARIABLE_UPVALUE:
                return va.slot_scope is vb.slot_scope
            if va.type == AST_VARIABLE.AST_VARIABLE_GLOBAL:
                return va.name == vb.name
            if va.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                return Ast._expressions_equivalent(va.table, vb.table) and Ast._expressions_equivalent(
                    va.table_index, vb.table_index
                )
            return False

        return False

    def _clone_expression_shallow(self, expression: Expression) -> Expression:
        clone = self.new_expression(expression.type)
        clone.assign_from(expression)
        return clone

    def _replace_slot_in_expression(
        self,
        expression: Optional[Expression],
        slot: int,
        replacement: Expression,
        target_scope: Optional[ScopeCell] = None,
    ) -> int:
        if expression is None:
            return 0

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
            var = expression.variable
            if (
                var.type == AST_VARIABLE.AST_VARIABLE_SLOT
                and var.slot == slot
                and (target_scope is None or var.slot_scope is target_scope)
            ):
                expression.assign_from(self._clone_expression_shallow(replacement))
                return 1
            if var.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                replaced = 0
                replaced += self._replace_slot_in_expression(
                    var.table, slot, replacement, target_scope
                )
                replaced += self._replace_slot_in_expression(
                    var.table_index, slot, replacement, target_scope
                )
                return replaced
            return 0

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
            replaced = self._replace_slot_in_expression(
                expression.function_call.function, slot, replacement, target_scope
            )
            for arg in expression.function_call.arguments:
                replaced += self._replace_slot_in_expression(
                    arg, slot, replacement, target_scope
                )
            replaced += self._replace_slot_in_expression(
                expression.function_call.multres_argument, slot, replacement, target_scope
            )
            return replaced

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
            replaced = 0
            for field in expression.table.fields:
                replaced += self._replace_slot_in_expression(
                    field.key, slot, replacement, target_scope
                )
                replaced += self._replace_slot_in_expression(
                    field.value, slot, replacement, target_scope
                )
            replaced += self._replace_slot_in_expression(
                expression.table.multres_field, slot, replacement, target_scope
            )
            return replaced

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            replaced = self._replace_slot_in_expression(
                expression.binary_operation.left_operand, slot, replacement, target_scope
            )
            replaced += self._replace_slot_in_expression(
                expression.binary_operation.right_operand, slot, replacement, target_scope
            )
            return replaced

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            return self._replace_slot_in_expression(
                expression.unary_operation.operand, slot, replacement, target_scope
            )

        return 0

    def _replace_slot_in_statement(
        self,
        statement: Statement,
        slot: int,
        replacement: Expression,
        target_scope: Optional[ScopeCell] = None,
    ) -> int:
        replaced = 0
        for idx in range(len(statement.assignment.expressions)):
            replaced += self._replace_slot_in_expression(
                statement.assignment.expressions[idx], slot, replacement, target_scope
            )
        replaced += self._replace_slot_in_expression(
            statement.assignment.multres_return, slot, replacement, target_scope
        )

        for variable in statement.assignment.variables:
            if variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                continue
            replaced += self._replace_slot_in_expression(
                variable.table, slot, replacement, target_scope
            )
            replaced += self._replace_slot_in_expression(
                variable.table_index, slot, replacement, target_scope
            )
        return replaced

    def _mark_method_call_if_possible(self, statement: Statement) -> None:
        call_expr: Optional[Expression] = None
        if (
            statement.type == AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL
            and statement.assignment.expressions
            and statement.assignment.expressions[-1].type
            == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
        ):
            call_expr = statement.assignment.expressions[-1]
        elif (
            statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
            and len(statement.assignment.expressions) == 1
            and statement.assignment.expressions[-1].type
            == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
        ):
            call_expr = statement.assignment.expressions[-1]

        if call_expr is None:
            return

        function_call = call_expr.function_call
        if (
            function_call is None
            or function_call.function is None
            or function_call.function.type != AST_EXPRESSION.AST_EXPRESSION_VARIABLE
            or function_call.function.variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
            or function_call.function.variable.table is None
            or not function_call.arguments
        ):
            return

        receiver = function_call.function.variable.table
        first_arg = function_call.arguments[0]
        if Ast._expressions_equivalent(receiver, first_arg):
            function_call.is_method = True
            del function_call.arguments[0]

    @staticmethod
    def _bool_constant_value(expression: Optional[Expression]) -> Optional[bool]:
        if (
            expression is None
            or expression.type != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
        ):
            return None
        if expression.constant.type == AST_CONSTANT.AST_CONSTANT_TRUE:
            return True
        if expression.constant.type == AST_CONSTANT.AST_CONSTANT_FALSE:
            return False
        return None

    def _build_condition_expression_from_condition_statement(
        self, statement: Statement
    ) -> Optional[Expression]:
        if statement.type != AST_STATEMENT.AST_STATEMENT_CONDITION:
            return None
        node_type = ConditionBuilder.get_node_type(
            statement.instruction.type, statement.condition.swapped
        )
        node = ConditionNode(node_type, expressions=statement.assignment.expressions)
        builder = ConditionBuilder(
            ConditionBuilderType.STATEMENT, self, INVALID_ID, INVALID_ID, INVALID_ID
        )
        return builder.build_expression(node)

    def _build_residual_condition_jump_expression(
        self, statement: Statement
    ) -> Optional[Expression]:
        if (
            statement.type != AST_STATEMENT.AST_STATEMENT_CONDITION
            or not statement.assignment.expressions
            or statement.instruction.type is None
        ):
            return None

        node_type = ConditionBuilder.get_node_type(
            statement.instruction.type, statement.condition.swapped
        )

        # Some residual comparison/equality condition statements keep only one
        # prebuilt expression. Treat these as falsy-tests so branch reconstruction
        # can still emit a valid condition.
        if len(statement.assignment.expressions) == 1 and node_type in (
            ConditionNodeType.LESS_THAN,
            ConditionNodeType.LESS_EQUAL,
            ConditionNodeType.GREATER_THEN,
            ConditionNodeType.GREATER_EQUAL,
            ConditionNodeType.NOT_LESS_THAN,
            ConditionNodeType.NOT_LESS_EQUAL,
            ConditionNodeType.NOT_GREATER_THEN,
            ConditionNodeType.NOT_GREATER_EQUAL,
            ConditionNodeType.EQUAL,
            ConditionNodeType.NOT_EQUAL,
        ):
            node_type = ConditionNodeType.FALSY_TEST

        if len(statement.assignment.expressions) < 2 and node_type in (
            ConditionNodeType.LESS_THAN,
            ConditionNodeType.LESS_EQUAL,
            ConditionNodeType.GREATER_THEN,
            ConditionNodeType.GREATER_EQUAL,
            ConditionNodeType.NOT_LESS_THAN,
            ConditionNodeType.NOT_LESS_EQUAL,
            ConditionNodeType.NOT_GREATER_THEN,
            ConditionNodeType.NOT_GREATER_EQUAL,
            ConditionNodeType.EQUAL,
            ConditionNodeType.NOT_EQUAL,
        ):
            return None

        node = ConditionNode(
            type=node_type,
            expressions=statement.assignment.expressions,
            inverted=False,
        )
        builder = ConditionBuilder(
            ConditionBuilderType.STATEMENT, self, INVALID_ID, INVALID_ID, INVALID_ID
        )
        expression = builder.build_expression(node)
        return self._simplify_safe_double_not_expression(expression)

    def _rewrite_residual_conditions(self, function: Function, block: list[Statement]) -> None:
        i = 0
        while i < len(block):
            statement = block[i]

            if statement.block:
                self._rewrite_residual_conditions(function, statement.block)

            if statement.type != AST_STATEMENT.AST_STATEMENT_CONDITION:
                i += 1
                continue

            if (
                statement.assignment.variables
                or not statement.assignment.expressions
                or statement.instruction.target == INVALID_ID
            ):
                i += 1
                continue

            target_label = function.get_label_from_id(statement.instruction.target)
            if target_label == INVALID_ID:
                i += 1
                continue

            branch_expression = self._build_residual_condition_jump_expression(statement)
            if branch_expression is None:
                i += 1
                continue

            goto_statement = self.new_statement(AST_STATEMENT.AST_STATEMENT_GOTO)
            goto_statement.instruction.id = statement.instruction.id
            goto_statement.instruction.type = BC_OP.BC_OP_JMP
            goto_statement.instruction.target = statement.instruction.target
            goto_statement.instruction.label = target_label

            statement.type = AST_STATEMENT.AST_STATEMENT_IF
            statement.assignment.expressions = [branch_expression]
            statement.block = [goto_statement]

            i += 1

    def _extract_single_slot_bool_assignment(
        self, statement: Statement
    ) -> Optional[tuple[AstVariable, bool]]:
        if statement.type not in (
            AST_STATEMENT.AST_STATEMENT_DECLARATION,
            AST_STATEMENT.AST_STATEMENT_ASSIGNMENT,
        ):
            return None
        if (
            len(statement.assignment.variables) != 1
            or len(statement.assignment.expressions) != 1
            or statement.assignment.variables[-1].type != AST_VARIABLE.AST_VARIABLE_SLOT
        ):
            return None
        bool_value = self._bool_constant_value(statement.assignment.expressions[-1])
        if bool_value is None:
            return None
        return statement.assignment.variables[-1], bool_value

    def _fold_if_goto_bool_assignments(
        self, function: Function, block: list[Statement]
    ) -> None:
        for statement in block:
            if statement.block:
                self._fold_if_goto_bool_assignments(function, statement.block)

        i = 0
        while i + 5 < len(block):
            if_statement = block[i]
            false_assignment_statement = block[i + 1]
            goto_end_statement = block[i + 2]
            true_label_statement = block[i + 3]
            true_assignment_statement = block[i + 4]
            end_label_statement = block[i + 5]

            if (
                if_statement.type != AST_STATEMENT.AST_STATEMENT_IF
                or len(if_statement.assignment.expressions) != 1
                or len(if_statement.block) != 1
                or if_statement.block[0].type
                not in (
                    AST_STATEMENT.AST_STATEMENT_GOTO,
                    AST_STATEMENT.AST_STATEMENT_BREAK,
                )
                or if_statement.block[0].instruction.type != BC_OP.BC_OP_JMP
                or goto_end_statement.type
                not in (
                    AST_STATEMENT.AST_STATEMENT_GOTO,
                    AST_STATEMENT.AST_STATEMENT_BREAK,
                )
                or goto_end_statement.instruction.type != BC_OP.BC_OP_JMP
                or true_label_statement.type != AST_STATEMENT.AST_STATEMENT_LABEL
                or end_label_statement.type != AST_STATEMENT.AST_STATEMENT_LABEL
            ):
                i += 1
                continue

            false_assignment = self._extract_single_slot_bool_assignment(
                false_assignment_statement
            )
            true_assignment = self._extract_single_slot_bool_assignment(
                true_assignment_statement
            )
            if false_assignment is None or true_assignment is None:
                i += 1
                continue

            false_variable, false_bool = false_assignment
            true_variable, true_bool = true_assignment
            if false_bool == true_bool:
                i += 1
                continue
            if (
                false_variable.slot != true_variable.slot
                or false_variable.slot_scope is not true_variable.slot_scope
            ):
                i += 1
                continue

            goto_true_statement = if_statement.block[0]
            if (
                not function.is_valid_label(goto_true_statement.instruction.label)
                or not function.is_valid_label(goto_end_statement.instruction.label)
                or goto_true_statement.instruction.label
                != true_label_statement.instruction.label
                or goto_end_statement.instruction.label
                != end_label_statement.instruction.label
            ):
                i += 1
                continue

            true_label = goto_true_statement.instruction.label
            end_label = goto_end_statement.instruction.label
            if (
                len(function.labels[true_label].jump_ids) != 1
                or function.labels[true_label].jump_ids[0]
                != goto_true_statement.instruction.id
                or len(function.labels[end_label].jump_ids) != 1
                or function.labels[end_label].jump_ids[0]
                != goto_end_statement.instruction.id
            ):
                i += 1
                continue

            replacement_expression = self._clone_expression_deep(
                if_statement.assignment.expressions[-1]
            )
            if true_bool is False and false_bool is True:
                replacement_expression = self._negate_condition_expression(
                    replacement_expression
                )
            replacement_expression = self._simplify_safe_double_not_expression(
                replacement_expression
            )

            false_assignment_statement.assignment.expressions[-1] = replacement_expression
            if (
                function.is_valid_label(if_statement.instruction.label)
                and not function.is_valid_label(false_assignment_statement.instruction.label)
            ):
                false_assignment_statement.instruction.label = (
                    if_statement.instruction.label
                )

            function.remove_jump(
                goto_true_statement.instruction.id,
                goto_true_statement.instruction.target,
            )
            function.remove_jump(
                goto_end_statement.instruction.id,
                goto_end_statement.instruction.target,
            )

            block[i] = false_assignment_statement
            del block[i + 1 : i + 6]
            continue

    def _inline_post_cleanup_nil_decl_temps(
        self, function: Function, block: list[Statement]
    ) -> None:
        def expression_slot_use_count(
            expression: Optional[Expression],
            slot: int,
            target_scope: Optional[ScopeCell],
        ) -> int:
            if expression is None:
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
                variable = expression.variable
                if variable.type == AST_VARIABLE.AST_VARIABLE_SLOT:
                    if variable.slot != slot:
                        return 0
                    if target_scope is None:
                        return 1
                    return 1 if variable.slot_scope is target_scope else 0
                if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    return expression_slot_use_count(
                        variable.table, slot, target_scope
                    ) + expression_slot_use_count(variable.table_index, slot, target_scope)
                return 0
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
                function_call = expression.function_call
                uses = expression_slot_use_count(function_call.function, slot, target_scope)
                uses += expression_slot_use_count(
                    function_call.multres_argument, slot, target_scope
                )
                for argument in function_call.arguments:
                    uses += expression_slot_use_count(argument, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
                uses = expression_slot_use_count(
                    expression.table.multres_field, slot, target_scope
                )
                for field in expression.table.constants.fields:
                    uses += expression_slot_use_count(field.key, slot, target_scope)
                    uses += expression_slot_use_count(field.value, slot, target_scope)
                for value in expression.table.constants.list:
                    uses += expression_slot_use_count(value, slot, target_scope)
                for field in expression.table.fields:
                    uses += expression_slot_use_count(field.key, slot, target_scope)
                    uses += expression_slot_use_count(field.value, slot, target_scope)
                return uses
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
                return expression_slot_use_count(
                    expression.binary_operation.left_operand, slot, target_scope
                ) + expression_slot_use_count(
                    expression.binary_operation.right_operand, slot, target_scope
                )
            if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
                return expression_slot_use_count(
                    expression.unary_operation.operand, slot, target_scope
                )
            return 0

        def statement_slot_use_count(
            statement: Statement, slot: int, target_scope: Optional[ScopeCell]
        ) -> int:
            uses = expression_slot_use_count(
                statement.assignment.multres_return, slot, target_scope
            )
            for expression in statement.assignment.expressions:
                uses += expression_slot_use_count(expression, slot, target_scope)
            for variable in statement.assignment.variables:
                if variable.type != AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
                    continue
                uses += expression_slot_use_count(variable.table, slot, target_scope)
                uses += expression_slot_use_count(variable.table_index, slot, target_scope)
            for nested in statement.block:
                uses += statement_slot_use_count(nested, slot, target_scope)
            return uses

        def is_nil_only_single_slot_declaration(statement: Statement) -> bool:
            if statement.type != AST_STATEMENT.AST_STATEMENT_DECLARATION:
                return False
            if len(statement.assignment.variables) != 1:
                return False
            if not statement.assignment.expressions:
                return True
            return (
                len(statement.assignment.expressions) == 1
                and statement.assignment.expressions[-1].type
                == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                and statement.assignment.expressions[-1].constant.type
                == AST_CONSTANT.AST_CONSTANT_NIL
            )

        def is_safe_inline_expression(expression: Optional[Expression]) -> bool:
            if (
                expression is None
                or not self._expression_is_side_effect_free(expression)
                or expression.type
                in (
                    AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL,
                    AST_EXPRESSION.AST_EXPRESSION_VARARG,
                )
            ):
                return False
            return True

        for statement in block:
            if statement.block:
                self._inline_post_cleanup_nil_decl_temps(function, statement.block)

        i = 0
        while i + 2 < len(block):
            declaration = block[i]
            assignment = block[i + 1]
            target_statement = block[i + 2]

            if (
                not is_nil_only_single_slot_declaration(declaration)
                or assignment.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                or len(declaration.assignment.variables) != 1
                or len(assignment.assignment.variables) != 1
                or len(assignment.assignment.expressions) != 1
                or declaration.assignment.variables[-1].type
                != AST_VARIABLE.AST_VARIABLE_SLOT
                or assignment.assignment.variables[-1].type
                != AST_VARIABLE.AST_VARIABLE_SLOT
                or declaration.assignment.variables[-1].slot
                != assignment.assignment.variables[-1].slot
                or declaration.assignment.variables[-1].slot_scope
                is not assignment.assignment.variables[-1].slot_scope
                or not is_safe_inline_expression(assignment.assignment.expressions[-1])
                or function.is_valid_label(declaration.instruction.label)
                or function.is_valid_label(assignment.instruction.label)
                or function.is_valid_label(target_statement.instruction.label)
            ):
                i += 1
                continue

            slot = declaration.assignment.variables[-1].slot
            slot_scope = declaration.assignment.variables[-1].slot_scope

            if statement_slot_use_count(target_statement, slot, slot_scope) != 1:
                i += 1
                continue

            if i + 3 < len(block):
                used_later = False
                for scan in range(i + 3, len(block)):
                    if statement_slot_use_count(block[scan], slot, slot_scope):
                        used_later = True
                        break
                if used_later:
                    i += 1
                    continue

            replaced = self._replace_slot_in_statement(
                target_statement,
                slot,
                assignment.assignment.expressions[-1],
                slot_scope,
            )
            if replaced != 1:
                i += 1
                continue

            if declaration.assignment.variables[-1].slot_scope is not None:
                function.slot_scope_collector.remove_scope(
                    declaration.assignment.variables[-1].slot,
                    declaration.assignment.variables[-1].slot_scope,
                )

            del block[i : i + 2]
            continue

    def _negate_condition_expression(self, expression: Expression) -> Expression:
        cloned = self._clone_expression_deep(expression)
        if cloned.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            flip_map: dict[AST_BINARY_OPERATION, AST_BINARY_OPERATION] = {
                AST_BINARY_OPERATION.AST_BINARY_EQUAL: AST_BINARY_OPERATION.AST_BINARY_NOT_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_NOT_EQUAL: AST_BINARY_OPERATION.AST_BINARY_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_LESS_THAN: AST_BINARY_OPERATION.AST_BINARY_GREATER_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_GREATER_EQUAL: AST_BINARY_OPERATION.AST_BINARY_LESS_THAN,
                AST_BINARY_OPERATION.AST_BINARY_LESS_EQUAL: AST_BINARY_OPERATION.AST_BINARY_GREATER_THEN,
                AST_BINARY_OPERATION.AST_BINARY_GREATER_THEN: AST_BINARY_OPERATION.AST_BINARY_LESS_EQUAL,
            }
            if cloned.binary_operation.type in flip_map:
                cloned.binary_operation.type = flip_map[cloned.binary_operation.type]
                return cloned

        negated = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION)
        negated.unary_operation.type = AST_UNARY_OPERATION.AST_UNARY_NOT
        negated.unary_operation.operand = cloned
        return negated

    def peephole_optimize_block(self, function: Function, block: list[Statement]) -> None:
        i = 0
        while i < len(block):
            statement = block[i]
            if statement.block:
                self.peephole_optimize_block(function, statement.block)

            self._mark_method_call_if_possible(statement)

            if i > 0:
                prev = block[i - 1]
                if (
                    prev.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT
                    and len(prev.assignment.variables) == 1
                    and prev.assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                    and len(prev.assignment.expressions) == 1
                    and prev.assignment.expressions[-1].type
                    in (
                        AST_EXPRESSION.AST_EXPRESSION_VARIABLE,
                        AST_EXPRESSION.AST_EXPRESSION_CONSTANT,
                    )
                    and not function.is_valid_label(prev.instruction.label)
                    and not function.is_valid_label(statement.instruction.label)
                ):
                    slot = prev.assignment.variables[-1].slot
                    replacement = prev.assignment.expressions[-1]
                    replaced = self._replace_slot_in_statement(
                        statement,
                        slot,
                        replacement,
                        prev.assignment.variables[-1].slot_scope,
                    )
                    if replaced:
                        self._mark_method_call_if_possible(statement)
                        del block[i - 1]
                        i -= 1
                        continue

            i += 1

    @staticmethod
    def _clone_variable(variable: AstVariable) -> AstVariable:
        return AstVariable(
            type=variable.type,
            slot=variable.slot,
            slot_scope=variable.slot_scope,
            name=variable.name,
            table=variable.table,
            table_index=variable.table_index,
            is_multres=variable.is_multres,
            multres_index=variable.multres_index,
        )

    def _cleanup_pass1(
        self,
        function: Function,
        block: list[Statement],
        variable_counter: int,
        iterator_counter: int,
        block_info: BlockInfo,
    ) -> tuple[int, int]:
        i = 0
        while i < len(block):
            statement = block[i]
            t = statement.type

            if t == AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR:
                if (
                    statement.assignment.expressions
                    and statement.assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                    and statement.assignment.expressions[-1].constant.type
                    == AST_CONSTANT.AST_CONSTANT_NUMBER
                    and statement.assignment.expressions[-1].constant.number == 1
                ):
                    statement.assignment.expressions.pop()

            if t in (
                AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR,
                AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
            ):
                if t == AST_STATEMENT.AST_STATEMENT_GENERIC_FOR:
                    while (
                        len(statement.assignment.expressions) > 1
                        and statement.assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                        and statement.assignment.expressions[-1].constant.type
                        == AST_CONSTANT.AST_CONSTANT_NIL
                    ):
                        statement.assignment.expressions.pop()

                if function.has_debug_info:
                    for j in range(len(statement.assignment.variables) - 1, -1, -1):
                        statement.assignment.variables[j].slot_scope.scope.name = (
                            statement.locals.names[j]
                        )
                else:
                    for j in range(len(statement.assignment.variables)):
                        statement.assignment.variables[j].slot_scope.scope.name = (
                            self._format_iter_name(function, iterator_counter)
                        )
                        iterator_counter += 1

                variable_counter, iterator_counter = self.clean_up_block(
                    function, statement.block, variable_counter, iterator_counter, None
                )
                i += 1
                continue

            if t == AST_STATEMENT.AST_STATEMENT_LOOP:
                # Descend into nested repeat-until blocks.
                current_block = statement.block
                while current_block:
                    if current_block[-1].type == AST_STATEMENT.AST_STATEMENT_DECLARATION:
                        current_block = current_block[-1].block
                        continue
                    if (
                        current_block[-1].type != AST_STATEMENT.AST_STATEMENT_GOTO
                        or current_block[-1].instruction.target != statement.instruction.id
                        or function.is_valid_label(current_block[-1].instruction.label)
                        or len(current_block) < 2
                    ):
                        break
                    second_last = current_block[-2]
                    if second_last.type == AST_STATEMENT.AST_STATEMENT_BREAK:
                        function.remove_jump(
                            current_block[-1].instruction.id,
                            current_block[-1].instruction.target,
                        )
                        function.remove_jump(
                            second_last.instruction.id,
                            second_last.instruction.target,
                        )
                        statement.type = AST_STATEMENT.AST_STATEMENT_REPEAT
                        statement.assignment.expressions.append(self.new_primitive(2))
                        second_last.type = AST_STATEMENT.AST_STATEMENT_EMPTY
                        current_block.pop()
                    elif second_last.type == AST_STATEMENT.AST_STATEMENT_IF:
                        if (
                            len(second_last.block) == 1
                            and second_last.block[-1].type
                            == AST_STATEMENT.AST_STATEMENT_BREAK
                        ):
                            function.remove_jump(
                                current_block[-1].instruction.id,
                                current_block[-1].instruction.target,
                            )
                            function.remove_jump(
                                second_last.block[-1].instruction.id,
                                second_last.block[-1].instruction.target,
                            )
                            statement.type = AST_STATEMENT.AST_STATEMENT_REPEAT
                            statement.assignment.expressions.append(
                                second_last.assignment.expressions[-1]
                            )
                            second_last.type = AST_STATEMENT.AST_STATEMENT_EMPTY
                            current_block.pop()
                    break

                # If this is still LOOP, check while-loop patterns.
                if statement.type == AST_STATEMENT.AST_STATEMENT_LOOP:
                    if (
                        statement.block
                        and statement.block[-1].type
                        == AST_STATEMENT.AST_STATEMENT_GOTO
                    ):
                        if (
                            statement.instruction.id
                            == statement.block[-1].instruction.target
                        ):
                            function.remove_jump(
                                statement.block[-1].instruction.id,
                                statement.block[-1].instruction.target,
                            )
                            statement.type = AST_STATEMENT.AST_STATEMENT_WHILE
                            statement.assignment.expressions.append(
                                self.new_primitive(2)
                            )
                            statement.block[-1].type = (
                                AST_STATEMENT.AST_STATEMENT_EMPTY
                            )
                        elif len(block) != 1:
                            # Backwards IF-chain scan for while(compound_condition)
                            # Check the leading loop condition.
                            j = i - 1
                            while (
                                j >= 0
                                and block[j].type == AST_STATEMENT.AST_STATEMENT_IF
                                and not block[j].block
                            ):
                                if not function.is_valid_label(
                                    block[j].instruction.label
                                ):
                                    j -= 1
                                    continue
                                if (
                                    function.is_valid_label(
                                        statement.instruction.label
                                    )
                                    or function.labels[
                                        block[j].instruction.label
                                    ].target
                                    != statement.block[-1].instruction.target
                                ):
                                    break
                                function.remove_jump(
                                    statement.block[-1].instruction.id,
                                    statement.block[-1].instruction.target,
                                )
                                statement.type = AST_STATEMENT.AST_STATEMENT_WHILE
                                statement.instruction.label = (
                                    block[j].instruction.label
                                )

                                while i != j:
                                    expression = self.new_expression(
                                        AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                                    )
                                    expression.binary_operation.type = (
                                        AST_BINARY_OPERATION.AST_BINARY_OR
                                    )
                                    expression.binary_operation.right_operand = (
                                        self.new_primitive(2)
                                    )
                                    expression.binary_operation.left_operand = (
                                        block[i - 1].assignment.expressions[-1]
                                    )

                                    if block[i].assignment.expressions:
                                        block[
                                            i - 1
                                        ].assignment.expressions[-1] = (
                                            self.new_expression(
                                                AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                                            )
                                        )
                                        block[
                                            i - 1
                                        ].assignment.expressions[
                                            -1
                                        ].binary_operation.type = (
                                            AST_BINARY_OPERATION.AST_BINARY_AND
                                        )
                                        block[
                                            i - 1
                                        ].assignment.expressions[
                                            -1
                                        ].binary_operation.right_operand = (
                                            block[i].assignment.expressions[-1]
                                        )
                                        block[
                                            i - 1
                                        ].assignment.expressions[
                                            -1
                                        ].binary_operation.left_operand = expression
                                        block[i].assignment.expressions[-1] = (
                                            block[
                                                i - 1
                                            ].assignment.expressions[-1]
                                        )
                                    else:
                                        if not block[i].assignment.expressions:
                                            block[i].assignment.expressions.append(
                                                expression
                                            )
                                        else:
                                            block[i].assignment.expressions[0] = (
                                                expression
                                            )

                                    del block[i - 1]
                                    i -= 1

                                statement.block[-1].type = (
                                    AST_STATEMENT.AST_STATEMENT_EMPTY
                                )
                                break
                        elif (
                            block_info.previous_block is not None
                            and block_info.previous_block.index != INVALID_ID
                            and block_info.previous_block.index
                            < len(block_info.previous_block.block)
                            and block_info.previous_block.block[
                                block_info.previous_block.index
                            ]
                            is not None
                            and block_info.previous_block.block[
                                block_info.previous_block.index
                            ].type
                            == AST_STATEMENT.AST_STATEMENT_IF
                            and not function.is_valid_label(
                                statement.instruction.label
                            )
                        ):
                            previous_if = block_info.previous_block.block[
                                block_info.previous_block.index
                            ]
                            if function.is_valid_label(
                                previous_if.instruction.label
                            ):
                                if (
                                    function.labels[
                                        previous_if.instruction.label
                                    ].target
                                    == statement.block[-1].instruction.target
                                ):
                                    function.remove_jump(
                                        statement.block[-1].instruction.id,
                                        statement.block[-1].instruction.target,
                                    )
                                    statement.type = (
                                        AST_STATEMENT.AST_STATEMENT_WHILE
                                    )
                                    statement.assignment.expressions.append(
                                        previous_if.assignment.expressions[-1]
                                    )
                                    statement.instruction.label = (
                                        previous_if.instruction.label
                                    )
                                    statement.block[-1].type = (
                                        AST_STATEMENT.AST_STATEMENT_EMPTY
                                    )
                                    block_info.previous_block.block[
                                        block_info.previous_block.index
                                    ] = statement
                            else:
                                # Parent-block backwards IF-chain scan
                                # Check the trailing loop condition.
                                pb = block_info.previous_block
                                j = pb.index - 1
                                found_parent_while = False
                                while (
                                    j >= 0
                                    and pb.block[j] is not None
                                    and pb.block[j].type
                                    == AST_STATEMENT.AST_STATEMENT_IF
                                    and not pb.block[j].block
                                ):
                                    if not function.is_valid_label(
                                        pb.block[j].instruction.label
                                    ):
                                        j -= 1
                                        continue
                                    if (
                                        function.labels[
                                            pb.block[j].instruction.label
                                        ].target
                                        != statement.block[
                                            -1
                                        ].instruction.target
                                    ):
                                        break
                                    function.remove_jump(
                                        statement.block[-1].instruction.id,
                                        statement.block[
                                            -1
                                        ].instruction.target,
                                    )
                                    statement.type = (
                                        AST_STATEMENT.AST_STATEMENT_WHILE
                                    )
                                    and_expr = self.new_expression(
                                        AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                                    )
                                    and_expr.binary_operation.type = (
                                        AST_BINARY_OPERATION.AST_BINARY_AND
                                    )
                                    and_expr.binary_operation.right_operand = (
                                        pb.block[
                                            pb.index
                                        ].assignment.expressions[-1]
                                    )
                                    statement.assignment.expressions.append(
                                        and_expr
                                    )
                                    statement.instruction.label = (
                                        pb.block[j].instruction.label
                                    )
                                    pb.block[j].instruction.label = INVALID_ID

                                    while j != pb.index - 1:
                                        expression = self.new_expression(
                                            AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                                        )
                                        expression.binary_operation.type = (
                                            AST_BINARY_OPERATION.AST_BINARY_OR
                                        )
                                        expression.binary_operation.right_operand = self.new_primitive(
                                            2
                                        )
                                        expression.binary_operation.left_operand = pb.block[
                                            j
                                        ].assignment.expressions[
                                            -1
                                        ]

                                        if (
                                            statement.assignment.expressions[
                                                -1
                                            ].binary_operation.left_operand
                                            is not None
                                        ):
                                            pb.block[
                                                j
                                            ].assignment.expressions[
                                                -1
                                            ] = self.new_expression(
                                                AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
                                            )
                                            pb.block[
                                                j
                                            ].assignment.expressions[
                                                -1
                                            ].binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_AND
                                            pb.block[
                                                j
                                            ].assignment.expressions[
                                                -1
                                            ].binary_operation.right_operand = (
                                                expression
                                            )
                                            pb.block[
                                                j
                                            ].assignment.expressions[
                                                -1
                                            ].binary_operation.left_operand = statement.assignment.expressions[
                                                -1
                                            ].binary_operation.left_operand
                                            statement.assignment.expressions[
                                                -1
                                            ].binary_operation.left_operand = pb.block[
                                                j
                                            ].assignment.expressions[
                                                -1
                                            ]
                                        else:
                                            statement.assignment.expressions[
                                                -1
                                            ].binary_operation.left_operand = (
                                                expression
                                            )

                                        pb.block[j].type = (
                                            AST_STATEMENT.AST_STATEMENT_EMPTY
                                        )
                                        j += 1

                                    statement.block[-1].type = (
                                        AST_STATEMENT.AST_STATEMENT_EMPTY
                                    )
                                    pb.block[pb.index] = statement
                                    found_parent_while = True
                                    break

                variable_counter, iterator_counter = self.clean_up_block(
                    function, statement.block, variable_counter, iterator_counter, None
                )
                i += 1
                continue

            if t == AST_STATEMENT.AST_STATEMENT_BREAK:
                function.remove_jump(statement.instruction.id, statement.instruction.target)
                i += 1
                continue

            if t == AST_STATEMENT.AST_STATEMENT_DECLARATION:
                while (
                    statement.assignment.expressions
                    and statement.assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                    and statement.assignment.expressions[-1].constant.type
                    == AST_CONSTANT.AST_CONSTANT_NIL
                ):
                    statement.assignment.expressions.pop()

                if statement.locals is not None:
                    for j in range(len(statement.assignment.variables) - 1, -1, -1):
                        statement.assignment.variables[j].slot_scope.scope.name = (
                            statement.locals.names[j]
                        )

                variable_counter, iterator_counter = self.clean_up_block(
                    function, statement.block, variable_counter, iterator_counter, None
                )
                i += 1
                continue

            if t == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                if (
                    len(statement.assignment.variables) == 1
                    and statement.assignment.variables[-1].type == AST_VARIABLE.AST_VARIABLE_SLOT
                    and statement.assignment.variables[-1].slot_scope is not None
                    and not statement.assignment.variables[-1].slot_scope.scope.usages
                    and len(statement.assignment.expressions) == 1
                    and statement.assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_TABLE
                    and len(statement.assignment.expressions[-1].table.fields) == 1
                    and not statement.assignment.expressions[-1].table.constants.list
                    and not statement.assignment.expressions[-1].table.constants.fields
                    and statement.assignment.expressions[-1].table.multres_field is None
                ):
                    function.slot_scope_collector.remove_scope(
                        statement.assignment.variables[-1].slot,
                        statement.assignment.variables[-1].slot_scope,
                    )
                    statement.assignment.variables[-1].type = AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                    statement.assignment.variables[-1].table = statement.assignment.expressions[-1]
                    statement.assignment.variables[-1].table_index = (
                        statement.assignment.expressions[-1].table.fields[-1].key
                    )
                    statement.assignment.expressions[-1] = (
                        statement.assignment.expressions[-1].table.fields[-1].value
                    )
                    statement.assignment.variables[-1].table.table.fields.pop()
                    i += 1
                    continue

                declaration_variables: list[AstVariable] = []
                for var in statement.assignment.variables:
                    if var.type != AST_VARIABLE.AST_VARIABLE_SLOT:
                        statement.assignment.forward_declaration = True
                        continue
                    if var.slot_scope is None or bool(var.slot_scope.scope.name):
                        statement.assignment.forward_declaration = True
                        continue
                    var.slot_scope.scope.name = self._format_var_name(
                        function, variable_counter
                    )
                    variable_counter += 1
                    declaration_variables.append(var)

                if declaration_variables:
                    block.insert(i, None)  # type: ignore[arg-type]
                    i += 1

                    for decl_var in declaration_variables:
                        declaration_target_block = block
                        declaration_target_index = i - 1
                        current_block_info = block_info

                        while current_block_info.previous_block is not None:
                            current_block_info = current_block_info.previous_block
                            if current_block_info.index == len(current_block_info.block) - 1:
                                continue

                            current_stmt = current_block_info.block[current_block_info.index]
                            scope_end = decl_var.slot_scope.scope.scope_end

                            if current_stmt.type == AST_STATEMENT.AST_STATEMENT_IF:
                                if (
                                    current_block_info.block[current_block_info.index + 1].type
                                    == AST_STATEMENT.AST_STATEMENT_ELSE
                                ):
                                    if (
                                        scope_end
                                        <= current_stmt.block[-1].instruction.id
                                    ):
                                        break
                                    if current_block_info.index == 0:
                                        break
                                    declaration_target_block = current_block_info.block
                                    declaration_target_index = (
                                        current_block_info.index - 1
                                    )
                                    statement.assignment.forward_declaration = True
                                    continue

                            if current_stmt.type in (
                                AST_STATEMENT.AST_STATEMENT_IF,
                                AST_STATEMENT.AST_STATEMENT_ELSE,
                            ):
                                next_stmt = current_block_info.block[
                                    current_block_info.index + 1
                                ]
                                if (
                                    next_stmt.type
                                    in (
                                        AST_STATEMENT.AST_STATEMENT_EMPTY,
                                        AST_STATEMENT.AST_STATEMENT_GOTO,
                                        AST_STATEMENT.AST_STATEMENT_BREAK,
                                    )
                                    and next_stmt.instruction.type == BC_OP.BC_OP_JMP
                                ):
                                    if scope_end < next_stmt.instruction.id:
                                        break
                                    offset = (
                                        2
                                        if current_stmt.type
                                        == AST_STATEMENT.AST_STATEMENT_ELSE
                                        else 1
                                    )
                                    if current_block_info.index < offset:
                                        break
                                    declaration_target_block = current_block_info.block
                                    declaration_target_index = (
                                        current_block_info.index - offset
                                    )
                                    statement.assignment.forward_declaration = True
                                    continue

                                target = function.labels[next_stmt.instruction.label].target
                                if scope_end < target:
                                    break
                                offset = (
                                    2
                                    if current_stmt.type
                                    == AST_STATEMENT.AST_STATEMENT_ELSE
                                    else 1
                                )
                                if current_block_info.index < offset:
                                    break
                                declaration_target_block = current_block_info.block
                                declaration_target_index = current_block_info.index - offset
                                statement.assignment.forward_declaration = True
                                continue

                            break

                        target_stmt = declaration_target_block[declaration_target_index]
                        if target_stmt is None:
                            target_stmt = self.new_statement(
                                AST_STATEMENT.AST_STATEMENT_DECLARATION
                            )
                            target_stmt.assignment.forward_declaration = True
                            target_stmt.instruction.target = (
                                decl_var.slot_scope.scope.scope_begin
                            )
                            declaration_target_block[declaration_target_index] = target_stmt

                        target_stmt.assignment.variables.append(decl_var)

                    if not statement.assignment.forward_declaration:
                        statement.type = AST_STATEMENT.AST_STATEMENT_DECLARATION
                        statement.assignment.forward_declaration = True
                        prev_stmt = block[i - 1]
                        if prev_stmt is not None:
                            statement.instruction.target = prev_stmt.instruction.target
                        block[i - 1] = None  # type: ignore[index]

                        while (
                            statement.assignment.expressions
                            and statement.assignment.expressions[-1].type
                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            and statement.assignment.expressions[-1].constant.type
                            == AST_CONSTANT.AST_CONSTANT_NIL
                        ):
                            statement.assignment.expressions.pop()

                    if block[i - 1] is None:
                        i -= 1
                        del block[i]

                if statement.type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                    while (
                        len(statement.assignment.expressions) > 1
                        and statement.assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                        and statement.assignment.expressions[-1].constant.type
                        == AST_CONSTANT.AST_CONSTANT_NIL
                    ):
                        statement.assignment.expressions.pop()

                i += 1
                continue

            if t == AST_STATEMENT.AST_STATEMENT_IF:
                block.insert(i, None)  # type: ignore[arg-type]
                i += 1
                statement = block[i]
                block_info.index = i
                variable_counter, iterator_counter = self.clean_up_block(
                    function, statement.block, variable_counter, iterator_counter, block_info
                )
                if (
                    not statement.block
                    and statement.assignment.expressions
                    and statement.assignment.expressions[-1].type
                    == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                    and statement.assignment.expressions[-1].constant.type
                    == AST_CONSTANT.AST_CONSTANT_FALSE
                ):
                    statement.type = AST_STATEMENT.AST_STATEMENT_EMPTY

                if i != len(block) - 1 and block[i + 1].type == AST_STATEMENT.AST_STATEMENT_ELSE:
                    i += 1
                    if block[i - 1].type == AST_STATEMENT.AST_STATEMENT_EMPTY:
                        block[i].type = AST_STATEMENT.AST_STATEMENT_EMPTY
                        block[i + 1 : i + 1] = block[i].block
                        block[i].block.clear()
                    else:
                        block_info.index += 1
                        variable_counter, iterator_counter = self.clean_up_block(
                            function, block[i].block, variable_counter, iterator_counter, block_info
                        )
                        block_info.index -= 1
                        if not block[i].block:
                            block[i].type = AST_STATEMENT.AST_STATEMENT_EMPTY

                if block[block_info.index - 1] is not None:
                    block[block_info.index - 1].instruction.target = block[
                        block_info.index
                    ].instruction.id
                else:
                    del block[block_info.index - 1]
                    i -= 1

                i += 1
                continue

            if statement.block:
                variable_counter, iterator_counter = self.clean_up_block(
                    function, statement.block, variable_counter, iterator_counter, None
                )

            i += 1

        return variable_counter, iterator_counter

    def _cleanup_insert_labels(self, function: Function, block: list[Statement]) -> None:
        i = 0
        while i < len(block):
            if function.is_valid_label(block[i].instruction.label):
                block.insert(i, self.new_statement(AST_STATEMENT.AST_STATEMENT_LABEL))
                block[i].instruction.label = block[i + 1].instruction.label
                i += 1

            if block[i].type == AST_STATEMENT.AST_STATEMENT_EMPTY:
                del block[i]
                continue

            if block[i].type == AST_STATEMENT.AST_STATEMENT_GOTO:
                block[i].instruction.label = function.get_label_from_id(block[i].instruction.target)

            i += 1

    def _cleanup_finalize_declarations(self, function: Function, block: list[Statement]) -> None:
        labels: list[int] = []
        i = len(block) - 1
        while i >= 0:
            if block[i].type != AST_STATEMENT.AST_STATEMENT_DECLARATION:
                i -= 1
                continue

            if block[i].assignment.forward_declaration:
                j = i
                while j < len(block):
                    if block[j].type != AST_STATEMENT.AST_STATEMENT_LABEL:
                        j += 1
                        continue

                    if (
                        function.labels[block[j].instruction.label].jump_ids[0]
                        < block[i].instruction.target
                    ):
                        for k in range(len(labels) - 1, -1, -1):
                            if (
                                function.labels[block[labels[k]].instruction.label].jump_ids[-1]
                                >= function.labels[block[j].instruction.label].target
                            ):
                                j = labels[k]

                        block.insert(i, self.new_statement(AST_STATEMENT.AST_STATEMENT_DO))
                        j += 1
                        block[i].block = list(block[i + 1 : j])
                        del block[i + 1 : j]

                        if (
                            block[i].block
                            and block[i].block[-1].type == AST_STATEMENT.AST_STATEMENT_DO
                        ):
                            inner_do = block[i].block[-1]
                            insert_index = len(block[i].block) - 1
                            block[i].block[insert_index:insert_index] = inner_do.block
                            inner_do.block.clear()
                            block[i].block.pop()

                        break

                    if (
                        function.labels[block[j].instruction.label].jump_ids[-1]
                        > function.labels[block[j].instruction.label].target
                    ):
                        labels.append(j)
                    j += 1

                labels.clear()
                i -= 1
                continue

            if i == len(block) - 1:
                block.extend(block[i].block)
                block[i].block.clear()
                i -= 1
                continue

            block[i].block.insert(
                0, self.new_statement(AST_STATEMENT.AST_STATEMENT_DECLARATION)
            )
            block[i].block[0].assignment.variables = block[i].assignment.variables
            block[i].block[0].assignment.expressions = block[i].assignment.expressions
            block[i].type = AST_STATEMENT.AST_STATEMENT_DO
            i -= 1

    @staticmethod
    def get_block_index_from_id(block: list[Statement], id_: int) -> int:
        for i in range(len(block) - 1, -1, -1):
            if block[i].instruction.id == INVALID_ID or block[i].instruction.id >= id_:
                if block[i].instruction.id == id_:
                    return i
        return INVALID_ID

    @staticmethod
    def get_extended_id_from_statement(statement: Statement) -> int:
        if statement.type in (AST_STATEMENT.AST_STATEMENT_GOTO, AST_STATEMENT.AST_STATEMENT_BREAK):
            if statement.instruction.type == BC_OP.BC_OP_JMP:
                return statement.instruction.target
        return statement.instruction.id

    @staticmethod
    def check_valid_name(constant: AstConstant) -> None:
        s = constant.string
        if not s or s[0] < "A":
            return
        for ch in s:
            if ch < "0":
                return
            if ch in _INVALID_NAME_CHARS:
                return
        if s in _LUA_KEYWORDS:
            return
        constant.is_name = True

    def check_special_number(self, expression: Expression, is_cdata: bool = False) -> None:
        raw = bitcast_f64_to_u64(expression.constant.number)
        if (raw & DOUBLE_EXPONENT) != DOUBLE_SPECIAL:
            decompiler_assert(
                raw != DOUBLE_NEGATIVE_ZERO or is_cdata,
                "Number constant is negative zero",
                self.bytecode.file_path,
                "Ast::check_special_number",
                __file__,
                0,
            )
            return
        decompiler_assert(
            not (raw & DOUBLE_FRACTION),
            "Number constant is NaN",
            self.bytecode.file_path,
            "Ast::check_special_number",
            __file__,
            0,
        )
        if is_cdata:
            return
        expression.set_type(AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION)
        expression.binary_operation.type = AST_BINARY_OPERATION.AST_BINARY_DIVISION
        expression.binary_operation.left_operand = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_CONSTANT)
        expression.binary_operation.left_operand.constant.type = AST_CONSTANT.AST_CONSTANT_NUMBER
        expression.binary_operation.left_operand.constant.number = -1 if (raw & DOUBLE_SIGN) else 1
        expression.binary_operation.right_operand = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_CONSTANT)
        expression.binary_operation.right_operand.constant.type = AST_CONSTANT.AST_CONSTANT_NUMBER
        expression.binary_operation.right_operand.constant.number = 0

    @staticmethod
    def get_constant_type(expression: Expression) -> CONSTANT_TYPE:
        def is_valid_number_constant(number: float) -> bool:
            raw = bitcast_f64_to_u64(number)
            return (not (raw & DOUBLE_FRACTION)) if (raw & DOUBLE_EXPONENT) == DOUBLE_SPECIAL else raw != DOUBLE_NEGATIVE_ZERO

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT:
            if expression.constant.type == AST_CONSTANT.AST_CONSTANT_NIL:
                return CONSTANT_TYPE.NIL_CONSTANT
            if expression.constant.type in (
                AST_CONSTANT.AST_CONSTANT_FALSE,
                AST_CONSTANT.AST_CONSTANT_TRUE,
                AST_CONSTANT.AST_CONSTANT_STRING,
            ):
                return CONSTANT_TYPE.BOOL_CONSTANT
            if expression.constant.type == AST_CONSTANT.AST_CONSTANT_NUMBER:
                return CONSTANT_TYPE.NUMBER_CONSTANT
            return CONSTANT_TYPE.INVALID_CONSTANT

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            op = expression.binary_operation.type
            if op in (
                AST_BINARY_OPERATION.AST_BINARY_ADDITION,
                AST_BINARY_OPERATION.AST_BINARY_SUBTRACTION,
                AST_BINARY_OPERATION.AST_BINARY_MULTIPLICATION,
                AST_BINARY_OPERATION.AST_BINARY_DIVISION,
                AST_BINARY_OPERATION.AST_BINARY_EXPONENTATION,
                AST_BINARY_OPERATION.AST_BINARY_MODULO,
            ):
                if (
                    Ast.get_constant_type(expression.binary_operation.left_operand)
                    != CONSTANT_TYPE.NUMBER_CONSTANT
                    or Ast.get_constant_type(expression.binary_operation.right_operand)
                    != CONSTANT_TYPE.NUMBER_CONSTANT
                ):
                    return CONSTANT_TYPE.INVALID_CONSTANT
                l = expression.binary_operation.left_operand.constant.number
                r = expression.binary_operation.right_operand.constant.number
                if op == AST_BINARY_OPERATION.AST_BINARY_ADDITION:
                    number = l + r
                elif op == AST_BINARY_OPERATION.AST_BINARY_SUBTRACTION:
                    number = l - r
                elif op == AST_BINARY_OPERATION.AST_BINARY_MULTIPLICATION:
                    number = l * r
                elif op == AST_BINARY_OPERATION.AST_BINARY_DIVISION:
                    number = l / r
                elif op == AST_BINARY_OPERATION.AST_BINARY_EXPONENTATION:
                    number = math.pow(l, r)
                else:
                    number = math.fmod(l, r)
                if is_valid_number_constant(number):
                    return CONSTANT_TYPE.NUMBER_CONSTANT

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            op = expression.unary_operation.type
            if op == AST_UNARY_OPERATION.AST_UNARY_NOT:
                if Ast.get_constant_type(expression.unary_operation.operand) != CONSTANT_TYPE.INVALID_CONSTANT:
                    return CONSTANT_TYPE.BOOL_CONSTANT
            elif op == AST_UNARY_OPERATION.AST_UNARY_MINUS:
                operand = expression.unary_operation.operand
                if operand.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT:
                    if operand.constant.type == AST_CONSTANT.AST_CONSTANT_NUMBER:
                        if not is_valid_number_constant(-operand.constant.number):
                            return CONSTANT_TYPE.INVALID_CONSTANT
                        return CONSTANT_TYPE.NUMBER_CONSTANT
                    if operand.constant.type in (
                        AST_CONSTANT.AST_CONSTANT_CDATA_SIGNED,
                        AST_CONSTANT.AST_CONSTANT_CDATA_UNSIGNED,
                        AST_CONSTANT.AST_CONSTANT_CDATA_IMAGINARY,
                    ):
                        return CONSTANT_TYPE.NUMBER_CONSTANT
        return CONSTANT_TYPE.INVALID_CONSTANT

    def new_slot(self, slot: int) -> Expression:
        expression = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_VARIABLE)
        expression.variable.type = AST_VARIABLE.AST_VARIABLE_SLOT
        expression.variable.slot = slot
        return expression

    def new_literal(self, literal: int) -> Expression:
        expression = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_CONSTANT)
        expression.constant.type = AST_CONSTANT.AST_CONSTANT_NUMBER
        expression.constant.number = float(literal)
        return expression

    def new_signed_literal(self, signed_literal: int) -> Expression:
        expression = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_CONSTANT)
        expression.constant.type = AST_CONSTANT.AST_CONSTANT_NUMBER
        expression.constant.number = float(bitcast_u16_to_i16(signed_literal))
        return expression

    def new_primitive(self, primitive: int) -> Expression:
        expression = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_CONSTANT)
        if primitive == 0:
            expression.constant.type = AST_CONSTANT.AST_CONSTANT_NIL
        elif primitive == 1:
            expression.constant.type = AST_CONSTANT.AST_CONSTANT_FALSE
        elif primitive == 2:
            expression.constant.type = AST_CONSTANT.AST_CONSTANT_TRUE
        else:
            raise DecompilerError("Invalid primitive constant")
        return expression

    @staticmethod
    def get_label_from_next_statement(
        function: Function,
        block_info: BlockInfo,
        return_extended_label: bool,
        exclude_declaration: bool,
    ) -> int:
        if block_info.index == len(block_info.block) - 1:
            if block_info.previous_block is None:
                return INVALID_ID
            return Ast.get_label_from_next_statement(
                function, block_info.previous_block, return_extended_label, False
            )

        statement = block_info.block[block_info.index + 1]
        if exclude_declaration and statement.type == AST_STATEMENT.AST_STATEMENT_DECLARATION:
            if statement.block:
                statement = statement.block[0]
            elif block_info.index + 2 != len(block_info.block):
                statement = block_info.block[block_info.index + 2]
            else:
                if block_info.previous_block is None:
                    return INVALID_ID
                return Ast.get_label_from_next_statement(
                    function, block_info.previous_block, return_extended_label, False
                )

        if statement.type in (
            AST_STATEMENT.AST_STATEMENT_EMPTY,
            AST_STATEMENT.AST_STATEMENT_GOTO,
            AST_STATEMENT.AST_STATEMENT_BREAK,
        ):
            if return_extended_label and statement.instruction.type == BC_OP.BC_OP_JMP:
                return function.get_label_from_id(statement.instruction.target)
        return statement.instruction.label

    @staticmethod
    def is_valid_block(function: Function, block_info: BlockInfo, block_begin: int) -> bool:
        if block_info.index == len(block_info.block) - 1:
            if block_info.previous_block is None:
                return True
            return Ast.is_valid_block(function, block_info.previous_block, block_begin)

        next_statement = block_info.block[block_info.index + 1]
        block_end = (
            function.labels[next_statement.instruction.label].target
            if next_statement.instruction.label != INVALID_ID
            else next_statement.instruction.id
        )
        if block_end == INVALID_ID:
            return True
        if block_end > block_begin:
            return function.is_valid_block_range(block_begin, block_end - 1, False)
        return True

    def new_number(self, function: Function, index: int) -> Expression:
        expression = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_CONSTANT)
        expression.constant.type = AST_CONSTANT.AST_CONSTANT_NUMBER
        number_constant = function.get_number_constant(index)
        if number_constant.type == BC_KNUM.BC_KNUM_INT:
            expression.constant.number = float(bitcast_u32_to_i32(number_constant.integer))
        else:
            expression.constant.number = bitcast_u64_to_f64(number_constant.number)
            self.check_special_number(expression)
        return expression

    def new_string(self, function: Function, index: int) -> Expression:
        expression = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_CONSTANT)
        expression.constant.type = AST_CONSTANT.AST_CONSTANT_STRING
        expression.constant.string = function.get_constant(index).string
        return expression

    def new_table(self, function: Function, index: int) -> Expression:
        def new_table_constant(constant: TableConstant) -> Expression:
            expression = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_CONSTANT)
            if constant.type == BC_KTAB.BC_KTAB_NIL:
                expression.constant.type = AST_CONSTANT.AST_CONSTANT_NIL
            elif constant.type == BC_KTAB.BC_KTAB_FALSE:
                expression.constant.type = AST_CONSTANT.AST_CONSTANT_FALSE
            elif constant.type == BC_KTAB.BC_KTAB_TRUE:
                expression.constant.type = AST_CONSTANT.AST_CONSTANT_TRUE
            elif constant.type == BC_KTAB.BC_KTAB_INT:
                expression.constant.type = AST_CONSTANT.AST_CONSTANT_NUMBER
                expression.constant.number = float(bitcast_u32_to_i32(constant.integer))
            elif constant.type == BC_KTAB.BC_KTAB_NUM:
                expression.constant.type = AST_CONSTANT.AST_CONSTANT_NUMBER
                expression.constant.number = bitcast_u64_to_f64(constant.number)
                self.check_special_number(expression)
            elif constant.type == BC_KTAB.BC_KTAB_STR:
                expression.constant.type = AST_CONSTANT.AST_CONSTANT_STRING
                expression.constant.string = constant.string
            return expression

        expression = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_TABLE)
        constant = function.get_constant(index)
        expression.table.constants.list = [None] * len(constant.array)  # type: ignore[list-item]
        for i in range(len(expression.table.constants.list) - 1, -1, -1):
            expression.table.constants.list[i] = new_table_constant(constant.array[i])

        if self.minimize_diffs:
            false_field = AstTableField()
            true_field = AstTableField()
            number_fields: list[AstTableField] = []
            string_fields: list[AstTableField] = []

            for i in range(len(constant.table) - 1, -1, -1):
                key = new_table_constant(constant.table[i].key)
                value = new_table_constant(constant.table[i].value)
                if key.constant.type == AST_CONSTANT.AST_CONSTANT_FALSE:
                    false_field.key = key
                    false_field.value = value
                elif key.constant.type == AST_CONSTANT.AST_CONSTANT_TRUE:
                    true_field.key = key
                    true_field.value = value
                elif key.constant.type == AST_CONSTANT.AST_CONSTANT_NUMBER:
                    field = AstTableField(key=key)
                    field.value = value
                    number_fields.append(field)
                elif key.constant.type == AST_CONSTANT.AST_CONSTANT_STRING:
                    Ast.check_valid_name(key.constant)
                    field = AstTableField(key=key)
                    field.value = value
                    string_fields.append(field)
                else:
                    raise DecompilerError("Invalid table key type")

            number_fields.sort(key=lambda f: f.key.constant.number)
            string_fields.sort(key=lambda f: f.key.constant.string)

            if false_field.key is not None:
                expression.table.constants.fields.append(false_field)
            if true_field.key is not None:
                expression.table.constants.fields.append(true_field)
            expression.table.constants.fields.extend(number_fields)
            expression.table.constants.fields.extend(string_fields)
        else:
            expression.table.constants.fields = [AstTableField() for _ in constant.table]
            for i in range(len(expression.table.constants.fields) - 1, -1, -1):
                field = expression.table.constants.fields[i]
                field.key = new_table_constant(constant.table[i].key)
                if field.key.constant.type == AST_CONSTANT.AST_CONSTANT_STRING:
                    Ast.check_valid_name(field.key.constant)
                field.value = new_table_constant(constant.table[i].value)

        return expression

    def new_cdata(self, function: Function, index: int) -> Expression:
        expression = self.new_expression(AST_EXPRESSION.AST_EXPRESSION_CONSTANT)
        constant = function.get_constant(index)
        if constant.type == BC_KGC.BC_KGC_I64:
            expression.constant.type = AST_CONSTANT.AST_CONSTANT_CDATA_SIGNED
            expression.constant.signed_integer = bitcast_u64_to_i64(constant.cdata)
        elif constant.type == BC_KGC.BC_KGC_U64:
            expression.constant.type = AST_CONSTANT.AST_CONSTANT_CDATA_UNSIGNED
            expression.constant.unsigned_integer = constant.cdata
        elif constant.type == BC_KGC.BC_KGC_COMPLEX:
            expression.constant.type = AST_CONSTANT.AST_CONSTANT_CDATA_IMAGINARY
            expression.constant.number = bitcast_u64_to_f64(constant.cdata)
            self.check_special_number(expression, True)
        else:
            raise DecompilerError("Invalid cdata constant type")
        return expression


class Lua:
    UTF8_BOM = b"\xEF\xBB\xBF"
    NEW_LINE = "\r\n"

    def __init__(
        self,
        bytecode: Bytecode,
        ast: Ast,
        file_path: str,
        force_overwrite: bool,
        minimize_diffs: bool,
        unrestricted_ascii: bool,
        fail_on_unsupported_statements: bool,
        format_slot: str,
    ) -> None:
        self.bytecode = bytecode
        self.ast = ast
        self.file_path = file_path
        self.force_overwrite = force_overwrite
        self.minimize_diffs = minimize_diffs
        self.unrestricted_ascii = unrestricted_ascii
        self.fail_on_unsupported_statements = fail_on_unsupported_statements
        self.format_slot = format_slot
        self.write_buffer: list[str] = []
        self.indent_level = 0
        self.prototype_data_left = 0
        self.current_function_name_key = 0

    def __call__(self) -> None:
        verbose_push(f"Lua writer: {self.file_path}")
        try:
            print_progress_bar()
            self.prototype_data_left = self.bytecode.prototypes_total_size
            verbose_log("Write header")
            self.write_header()
            if self.ast.chunk and self.ast.chunk.block:
                verbose_log("Write main block")
                self.write_block(self.ast.chunk, self.ast.chunk.block)
            if self.ast.chunk:
                self.prototype_data_left -= self.ast.chunk.prototype.prototype_size
            print_progress_bar(
                self.bytecode.prototypes_total_size - self.prototype_data_left,
                self.bytecode.prototypes_total_size,
            )
            verbose_log("Flush output file")
            self.write_file()
            erase_progress_bar()
        finally:
            verbose_pop("Lua writer complete")

    def write_header(self) -> None:
        if not self.unrestricted_ascii:
            self.write_buffer.append(self.UTF8_BOM.decode("latin1"))
        if not self.bytecode.header_chunkname:
            return
        self.write("-- chunkname: ")
        self.write_string(self.bytecode.header_chunkname)
        self.write(self.NEW_LINE, self.NEW_LINE)

    def write_block(self, function: Function, block: list[Statement]) -> None:
        if not block:
            self.write_indent()
            self.write("-- block empty", self.NEW_LINE)
            return

        previous_function_name_key = self.current_function_name_key
        self.current_function_name_key = (
            function.level if self.minimize_diffs else function.id
        )
        previous_line_is_empty = True
        i = 0
        try:
            while i < len(block):
                statement = block[i]
                if not previous_line_is_empty:
                    prev_type = block[i - 1].type
                    if prev_type == AST_STATEMENT.AST_STATEMENT_RETURN:
                        if statement.type != AST_STATEMENT.AST_STATEMENT_RETURN:
                            previous_line_is_empty = True
                    elif prev_type in (
                        AST_STATEMENT.AST_STATEMENT_GOTO,
                        AST_STATEMENT.AST_STATEMENT_BREAK,
                    ):
                        if statement.type not in (
                            AST_STATEMENT.AST_STATEMENT_GOTO,
                            AST_STATEMENT.AST_STATEMENT_BREAK,
                        ):
                            previous_line_is_empty = True
                    elif prev_type == AST_STATEMENT.AST_STATEMENT_DECLARATION:
                        if statement.type != AST_STATEMENT.AST_STATEMENT_DECLARATION:
                            previous_line_is_empty = True
                    elif prev_type == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                        if statement.type != AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                            previous_line_is_empty = True
                    elif prev_type == AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL:
                        if statement.type != AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL:
                            previous_line_is_empty = True
                    elif prev_type == AST_STATEMENT.AST_STATEMENT_LABEL:
                        if statement.type != AST_STATEMENT.AST_STATEMENT_LABEL:
                            previous_line_is_empty = True
                    elif prev_type in (
                        AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR,
                        AST_STATEMENT.AST_STATEMENT_GENERIC_FOR,
                        AST_STATEMENT.AST_STATEMENT_IF,
                        AST_STATEMENT.AST_STATEMENT_ELSE,
                        AST_STATEMENT.AST_STATEMENT_WHILE,
                        AST_STATEMENT.AST_STATEMENT_REPEAT,
                        AST_STATEMENT.AST_STATEMENT_DO,
                    ):
                        previous_line_is_empty = True

                    if previous_line_is_empty:
                        self.write(self.NEW_LINE)

                t = statement.type
                if _verbose_enabled:
                    verbose_log(f"emit statement[{i}] type={t.name}")
                if t == AST_STATEMENT.AST_STATEMENT_RETURN:
                    self.write_indent()
                    if i != len(block) - 1:
                        self.write("do ")
                    self.write("return")
                    if statement.assignment.expressions or statement.assignment.multres_return is not None:
                        self.write(" ")
                        self.write_expression_list(
                            statement.assignment.expressions, statement.assignment.multres_return
                        )
                    if i != len(block) - 1:
                        self.write(" end")

                elif t == AST_STATEMENT.AST_STATEMENT_GOTO:
                    self.write_indent()
                    if 0 <= statement.instruction.label < len(function.labels):
                        self.write("goto ", function.labels[statement.instruction.label].name)
                    else:
                        self.write("goto label_invalid")

                elif t == AST_STATEMENT.AST_STATEMENT_NUMERIC_FOR:
                    self.write_indent()
                    self.write("for ")
                    self.write_variable(statement.assignment.variables[-1], False)
                    self.write(" = ")
                    self.write_expression(statement.assignment.expressions[0], False)
                    self.write(", ")
                    self.write_expression(statement.assignment.expressions[1], False)

                    if len(statement.assignment.expressions) == 3:
                        self.write(", ")
                        self.write_expression(statement.assignment.expressions[2], False)

                    self.write(" do", self.NEW_LINE)
                    self.indent_level += 1
                    self.write_block(function, statement.block)
                    self.indent_level -= 1
                    self.write_indent()
                    self.write("end")

                elif t == AST_STATEMENT.AST_STATEMENT_GENERIC_FOR:
                    self.write_indent()
                    self.write("for ")
                    self.write_assignment(
                        statement.assignment.variables,
                        statement.assignment.expressions,
                        " in ",
                        False,
                    )
                    self.write(" do", self.NEW_LINE)
                    self.indent_level += 1
                    self.write_block(function, statement.block)
                    self.indent_level -= 1
                    self.write_indent()
                    self.write("end")

                elif t == AST_STATEMENT.AST_STATEMENT_BREAK:
                    self.write_indent()
                    if i != len(block) - 1:
                        self.write("do ")
                    self.write("break")
                    if i != len(block) - 1:
                        self.write(" end")

                elif t == AST_STATEMENT.AST_STATEMENT_DECLARATION:
                    close_arg_variable: Optional[AstVariable] = None
                    if (
                        i == len(block) - 1
                        and i > 0
                        and len(statement.assignment.variables) == 1
                        and not statement.assignment.expressions
                        and block[i - 1].type == AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL
                        and len(block[i - 1].assignment.expressions) == 1
                        and block[i - 1].assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                    ):
                        close_call = block[i - 1].assignment.expressions[-1].function_call
                        if (
                            close_call.function is not None
                            and close_call.function.type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and close_call.function.variable.type
                            == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                            and close_call.function.variable.table is not None
                            and close_call.function.variable.table.type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and close_call.function.variable.table.variable.type
                            == AST_VARIABLE.AST_VARIABLE_GLOBAL
                            and close_call.function.variable.table.variable.name == "io"
                            and close_call.function.variable.table_index is not None
                            and close_call.function.variable.table_index.type
                            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            and close_call.function.variable.table_index.constant.type
                            == AST_CONSTANT.AST_CONSTANT_STRING
                            and close_call.function.variable.table_index.constant.string
                            == "close"
                            and len(close_call.arguments) == 1
                            and close_call.arguments[0].type
                            == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                        ):
                            close_arg_variable = close_call.arguments[0].variable

                    if close_arg_variable is not None:
                        self.write_indent()
                        self.write_variable(close_arg_variable, False)
                        self.write(" = nil")
                        self.write(self.NEW_LINE)
                        previous_line_is_empty = False
                        i += 1
                        continue

                    is_function_definition = False

                    if (
                        len(statement.assignment.variables) == 1
                        and len(statement.assignment.expressions) == 1
                        and statement.assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_FUNCTION
                    ):
                        is_function_definition = True
                        function_expr = statement.assignment.expressions[-1].function

                        if function_expr is not None and not function_expr.assignment_slot_is_upvalue:
                            variable_name = (
                                statement.assignment.variables[-1].slot_scope.scope.name
                                if statement.assignment.variables[-1].slot_scope is not None
                                else ""
                            )

                            for upvalue in function_expr.upvalues:
                                if (
                                    upvalue.slot_scope is not None
                                    and upvalue.slot_scope.scope.name == variable_name
                                ):
                                    is_function_definition = False
                                    break

                            if is_function_definition:
                                for used_global in function_expr.used_globals:
                                    if used_global == variable_name:
                                        is_function_definition = False
                                        break

                    if is_function_definition:
                        if not previous_line_is_empty:
                            self.write(self.NEW_LINE)
                        self.write_indent()
                        self.write("local function ")
                        self.write_variable(statement.assignment.variables[-1], False)
                        self.write_function_definition(statement.assignment.expressions[-1].function, False)

                        if i != len(block) - 1:
                            self.write(self.NEW_LINE, self.NEW_LINE)
                            previous_line_is_empty = True
                            i += 1
                            continue
                    else:
                        self.write_indent()
                        self.write("local ")
                        self.write_assignment(
                            statement.assignment.variables,
                            statement.assignment.expressions,
                            " = ",
                            False,
                        )

                elif t == AST_STATEMENT.AST_STATEMENT_ASSIGNMENT:
                    is_function_definition = False

                    if (
                        len(statement.assignment.variables) == 1
                        and len(statement.assignment.expressions) == 1
                        and statement.assignment.expressions[-1].type
                        == AST_EXPRESSION.AST_EXPRESSION_FUNCTION
                    ):
                        variable = statement.assignment.variables[-1]
                        while True:
                            if variable.type in (
                                AST_VARIABLE.AST_VARIABLE_SLOT,
                                AST_VARIABLE.AST_VARIABLE_UPVALUE,
                                AST_VARIABLE.AST_VARIABLE_GLOBAL,
                            ):
                                is_function_definition = True
                            elif (
                                variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                                and variable.table is not None
                                and variable.table.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                                and variable.table.variable is not None
                                and variable.table_index is not None
                                and variable.table_index.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                and variable.table_index.constant is not None
                                and variable.table_index.constant.is_name
                            ):
                                variable = variable.table.variable
                                continue
                            break

                    if is_function_definition:
                        if not previous_line_is_empty:
                            self.write(self.NEW_LINE)
                        self.write_indent()
                        self.write("function ")

                        func_expr = statement.assignment.expressions[-1].function
                        target = statement.assignment.variables[-1]
                        if (
                            target.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX
                            and target.table is not None
                            and target.table.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE
                            and target.table.variable is not None
                            and target.table_index is not None
                            and target.table_index.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            and target.table_index.constant is not None
                            and func_expr is not None
                            and len(func_expr.parameter_names) > 0
                            and func_expr.parameter_names[0] == "self"
                        ):
                            self.write_variable(target.table.variable, False)
                            self.write(":", target.table_index.constant.string)
                            self.write_function_definition(func_expr, True)
                        else:
                            self.write_variable(target, False)
                            self.write_function_definition(func_expr, False)

                        if i != len(block) - 1:
                            self.write(self.NEW_LINE, self.NEW_LINE)
                            previous_line_is_empty = True
                            i += 1
                            continue
                    else:
                        self.write_indent()
                        self.write_assignment(
                            statement.assignment.variables,
                            statement.assignment.expressions,
                            " = ",
                            bool(i),
                        )

                elif t == AST_STATEMENT.AST_STATEMENT_FUNCTION_CALL:
                    self.write_indent()
                    self.write_function_call(statement.assignment.expressions[-1].function_call, bool(i))

                elif t == AST_STATEMENT.AST_STATEMENT_IF:
                    self.write_indent()
                    self.write("if ")
                    self.write_condition_expression(statement)
                    self.write(" then", self.NEW_LINE)
                    self.indent_level += 1
                    self.write_block(function, statement.block)
                    self.indent_level -= 1
                    self.write_indent()

                    if i + 1 < len(block) and block[i + 1].type == AST_STATEMENT.AST_STATEMENT_ELSE:
                        i += 1
                        else_block = block[i].block

                        while True:
                            if len(else_block) == 1 and else_block[0].type == AST_STATEMENT.AST_STATEMENT_IF:
                                self.write("elseif ")
                                self.write_condition_expression(else_block[0])
                                self.write(" then", self.NEW_LINE)
                                self.indent_level += 1
                                self.write_block(function, else_block[0].block)
                                self.indent_level -= 1
                                self.write_indent()
                            elif (
                                len(else_block) == 2
                                and else_block[0].type == AST_STATEMENT.AST_STATEMENT_IF
                                and else_block[1].type == AST_STATEMENT.AST_STATEMENT_ELSE
                            ):
                                self.write("elseif ")
                                self.write_condition_expression(else_block[0])
                                self.write(" then", self.NEW_LINE)
                                self.indent_level += 1
                                self.write_block(function, else_block[0].block)
                                self.indent_level -= 1
                                self.write_indent()
                                else_block = else_block[1].block
                                continue
                            else:
                                self.write("else", self.NEW_LINE)
                                self.indent_level += 1
                                self.write_block(function, else_block)
                                self.indent_level -= 1
                                self.write_indent()

                            break

                    self.write("end")

                elif t == AST_STATEMENT.AST_STATEMENT_WHILE:
                    self.write_indent()
                    self.write("while ")
                    self.write_condition_expression(statement)
                    self.write(" do", self.NEW_LINE)
                    self.indent_level += 1
                    self.write_block(function, statement.block)
                    self.indent_level -= 1
                    self.write_indent()
                    self.write("end")

                elif t == AST_STATEMENT.AST_STATEMENT_REPEAT:
                    self.write_indent()
                    self.write("repeat", self.NEW_LINE)
                    self.indent_level += 1
                    self.write_block(function, statement.block)
                    self.indent_level -= 1
                    self.write_indent()
                    self.write("until ")
                    self.write_condition_expression(statement)

                elif t == AST_STATEMENT.AST_STATEMENT_DO:
                    self.write_indent()
                    self.write("do", self.NEW_LINE)
                    self.indent_level += 1
                    self.write_block(function, statement.block)
                    self.indent_level -= 1
                    self.write_indent()
                    self.write("end")

                elif t == AST_STATEMENT.AST_STATEMENT_LABEL:
                    self.write_indent()
                    if 0 <= statement.instruction.label < len(function.labels):
                        self.write("::", function.labels[statement.instruction.label].name, "::")
                    else:
                        self.write("::label_invalid::")

                elif t == AST_STATEMENT.AST_STATEMENT_EMPTY:
                    i += 1
                    continue

                else:
                    if self.fail_on_unsupported_statements:
                        instruction_type_name = (
                            statement.instruction.type.name
                            if statement.instruction.type is not None
                            else "UNKNOWN"
                        )
                        raise DecompilerError(
                            (
                                "Unsupported statement type in Lua writer "
                                f"({statement.type.name}, op={instruction_type_name}) "
                                f"at instruction id {statement.instruction.id}"
                            ),
                            self.file_path,
                            "Lua::write_block",
                            __file__,
                            0,
                        )
                    self.write_indent()
                    self.write("-- unsupported statement")

                self.write(self.NEW_LINE)
                previous_line_is_empty = False
                i += 1
        finally:
            self.current_function_name_key = previous_function_name_key

    def write_condition_expression(self, statement: Statement) -> None:
        expressions = statement.assignment.expressions
        if len(expressions) == 2:
            itype = statement.instruction.type
            swapped = statement.condition.swapped
            op = ""

            # Fallback for unresolved raw test nodes: invert to emitted branch condition.
            if itype == BC_OP.BC_OP_ISLT:
                op = "<=" if swapped else ">="
            elif itype == BC_OP.BC_OP_ISGE:
                op = ">" if swapped else "<"
            elif itype == BC_OP.BC_OP_ISLE:
                op = "<" if swapped else ">"
            elif itype == BC_OP.BC_OP_ISGT:
                op = ">=" if swapped else "<="
            elif itype in (
                BC_OP.BC_OP_ISEQV,
                BC_OP.BC_OP_ISEQS,
                BC_OP.BC_OP_ISEQN,
                BC_OP.BC_OP_ISEQP,
            ):
                op = "~="
            elif itype in (
                BC_OP.BC_OP_ISNEV,
                BC_OP.BC_OP_ISNES,
                BC_OP.BC_OP_ISNEN,
                BC_OP.BC_OP_ISNEP,
            ):
                op = "=="

            if op:
                self.write_expression(expressions[0], False)
                self.write(f" {op} ")
                self.write_expression(expressions[1], False)
                return

        if expressions:
            self.write_expression(expressions[-1], False)
        else:
            self.write("false")

    def write_expression(self, expression: Optional[Expression], use_parentheses: bool) -> None:
        if expression is None:
            self.write("nil")
            return
        if use_parentheses:
            self.write("(")

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT:
            c = expression.constant
            if c.type == AST_CONSTANT.AST_CONSTANT_NIL:
                self.write("nil")
            elif c.type == AST_CONSTANT.AST_CONSTANT_FALSE:
                self.write("false")
            elif c.type == AST_CONSTANT.AST_CONSTANT_TRUE:
                self.write("true")
            elif c.type == AST_CONSTANT.AST_CONSTANT_NUMBER:
                self.write_number(c.number)
            elif c.type == AST_CONSTANT.AST_CONSTANT_CDATA_SIGNED:
                self.write(str(c.signed_integer), "LL")
            elif c.type == AST_CONSTANT.AST_CONSTANT_CDATA_UNSIGNED:
                self.write(str(c.unsigned_integer), "ULL")
            elif c.type == AST_CONSTANT.AST_CONSTANT_CDATA_IMAGINARY:
                self.write_number(c.number)
                self.write("i")
            elif c.type == AST_CONSTANT.AST_CONSTANT_STRING:
                self.write("\"")
                self.write_string(c.string)
                self.write("\"")

        elif expression.type == AST_EXPRESSION.AST_EXPRESSION_VARARG:
            self.write("...")

        elif expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION:
            self.write("function")
            self.write_function_definition(expression.function, False)

        elif expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
            self.write_variable(expression.variable, False)

        elif expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
            self.write_function_call(expression.function_call, False)

        elif expression.type == AST_EXPRESSION.AST_EXPRESSION_TABLE:
            table = expression.table
            if (
                not table.constants.list
                and not table.constants.fields
                and not table.fields
                and table.multres_field is None
            ):
                self.write("{}")
            else:
                self.write("{", self.NEW_LINE)
                self.indent_level += 1
                self.write_indent()
                next_list_index = 1
                next_field_index = 0
                is_first_field = True

                if (
                    table.constants.list
                    and table.constants.list[0].type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                    and table.constants.list[0].constant.type != AST_CONSTANT.AST_CONSTANT_NIL
                ):
                    self.write("[0] = ")
                    self.write_expression(table.constants.list[0], False)
                    is_first_field = False

                while (
                    (table.multres_field is not None and next_list_index < table.multres_index)
                    or table.multres_field is None
                ):
                    if (
                        next_list_index < len(table.constants.list)
                        and table.constants.list[next_list_index].type
                        == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                        and table.constants.list[next_list_index].constant.type
                        != AST_CONSTANT.AST_CONSTANT_NIL
                    ):
                        if not is_first_field:
                            self.write(",", self.NEW_LINE)
                            self.write_indent()
                        self.write_expression(table.constants.list[next_list_index], False)
                        is_first_field = False
                        next_list_index += 1
                        continue

                    is_field_found = False
                    for fi in range(next_field_index, len(table.fields)):
                        field = table.fields[fi]
                        if (
                            field.key.type != AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                            or field.key.constant.type != AST_CONSTANT.AST_CONSTANT_NUMBER
                            or field.key.constant.number != next_list_index
                        ):
                            continue
                        is_field_found = True

                        while next_field_index < fi:
                            if not is_first_field:
                                self.write(",", self.NEW_LINE)
                                self.write_indent()

                            key = table.fields[next_field_index].key
                            if (
                                key.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                                and key.constant.is_name
                            ):
                                self.write(key.constant.string)
                            else:
                                self.write("[")
                                self.write_expression(key, False)
                                self.write("]")

                            self.write(" = ")
                            self.write_expression(table.fields[next_field_index].value, False)
                            is_first_field = False
                            next_field_index += 1

                        break

                    if is_field_found:
                        if not is_first_field:
                            self.write(",", self.NEW_LINE)
                            self.write_indent()

                        if (
                            table.multres_field is None
                            and next_field_index == len(table.fields) - 1
                            and not table.constants.fields
                            and (
                                not table.constants.list
                                or next_list_index >= len(table.constants.list) - 1
                            )
                        ):
                            value = table.fields[-1].value
                            if value.type in (
                                AST_EXPRESSION.AST_EXPRESSION_VARARG,
                                AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL,
                            ):
                                self.write_expression(value, True)
                            else:
                                self.write_expression(value, False)
                            next_list_index += 1
                            next_field_index += 1
                            break

                        self.write_expression(table.fields[next_field_index].value, False)
                        next_field_index += 1
                    elif table.multres_field is None and next_list_index >= len(table.constants.list):
                        break
                    else:
                        if not is_first_field:
                            self.write(",", self.NEW_LINE)
                            self.write_indent()
                        self.write("nil")

                    is_first_field = False
                    next_list_index += 1

                for li in range(next_list_index, len(table.constants.list)):
                    list_value = table.constants.list[li]
                    if (
                        list_value.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                        and list_value.constant.type == AST_CONSTANT.AST_CONSTANT_NIL
                    ):
                        continue

                    if not is_first_field:
                        self.write(",", self.NEW_LINE)
                        self.write_indent()

                    self.write("[", str(li), "] = ")
                    self.write_expression(list_value, False)
                    is_first_field = False

                for field in table.constants.fields:
                    if not is_first_field:
                        self.write(",", self.NEW_LINE)
                        self.write_indent()

                    if (
                        field.key.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                        and field.key.constant.is_name
                    ):
                        self.write(field.key.constant.string)
                    else:
                        self.write("[")
                        self.write_expression(field.key, False)
                        self.write("]")

                    self.write(" = ")
                    self.write_expression(field.value, False)
                    is_first_field = False

                for fi in range(next_field_index, len(table.fields)):
                    if not is_first_field:
                        self.write(",", self.NEW_LINE)
                        self.write_indent()

                    key = table.fields[fi].key
                    if (
                        key.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                        and key.constant.is_name
                    ):
                        self.write(key.constant.string)
                    else:
                        self.write("[")
                        self.write_expression(key, False)
                        self.write("]")

                    self.write(" = ")
                    self.write_expression(table.fields[fi].value, False)
                    is_first_field = False

                if table.multres_field is not None:
                    if not is_first_field:
                        self.write(",", self.NEW_LINE)
                        self.write_indent()
                    self.write_expression(table.multres_field, False)

                self.indent_level -= 1
                if self.minimize_diffs:
                    self.write(",")
                self.write(self.NEW_LINE)
                self.write_indent()
                self.write("}")

        elif expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            operator_precedence = self.get_operator_precedence(expression)
            operand_precedence = self.get_operator_precedence(
                expression.binary_operation.left_operand
            )
            parentheses = False

            if operand_precedence == operator_precedence:
                if operand_precedence in (3, 7):
                    parentheses = True
            elif operand_precedence < operator_precedence:
                parentheses = True
            elif (
                operator_precedence == 7
                and expression.binary_operation.left_operand.type
                == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
            ):
                left_constant = expression.binary_operation.left_operand.constant
                if left_constant.type in (
                    AST_CONSTANT.AST_CONSTANT_NUMBER,
                    AST_CONSTANT.AST_CONSTANT_CDATA_IMAGINARY,
                ):
                    if bitcast_f64_to_u64(left_constant.number) & DOUBLE_SIGN:
                        parentheses = True
                elif left_constant.type == AST_CONSTANT.AST_CONSTANT_CDATA_SIGNED:
                    if left_constant.signed_integer < 0:
                        parentheses = True

            self.write_expression(expression.binary_operation.left_operand, parentheses)

            if expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_ADDITION:
                self.write(" + ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_SUBTRACTION:
                self.write(" - ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_MULTIPLICATION:
                self.write(" * ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_DIVISION:
                self.write(" / ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_EXPONENTATION:
                self.write("^")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_MODULO:
                self.write(" % ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_CONCATENATION:
                self.write(" .. ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_LESS_THAN:
                self.write(" < ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_LESS_EQUAL:
                self.write(" <= ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_GREATER_THEN:
                self.write(" > ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_GREATER_EQUAL:
                self.write(" >= ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_EQUAL:
                self.write(" == ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_NOT_EQUAL:
                self.write(" ~= ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_AND:
                self.write(" and ")
            elif expression.binary_operation.type == AST_BINARY_OPERATION.AST_BINARY_OR:
                self.write(" or ")

            parentheses = False
            if (
                expression.binary_operation.right_operand is not None
                and expression.binary_operation.right_operand.type
                == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION
            ):
                operand_precedence = self.get_operator_precedence(
                    expression.binary_operation.right_operand
                )
                if operand_precedence == operator_precedence:
                    if operand_precedence in (2, 4, 5):
                        parentheses = True
                elif operand_precedence < operator_precedence:
                    parentheses = True

            self.write_expression(expression.binary_operation.right_operand, parentheses)

        elif expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            parentheses = self.get_operator_precedence(expression.unary_operation.operand) < 6

            if expression.unary_operation.type == AST_UNARY_OPERATION.AST_UNARY_MINUS:
                if (
                    not parentheses
                    and expression.unary_operation.operand.type
                    == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION
                    and expression.unary_operation.operand.unary_operation.type
                    == AST_UNARY_OPERATION.AST_UNARY_MINUS
                ):
                    parentheses = True
                self.write("-")
            elif expression.unary_operation.type == AST_UNARY_OPERATION.AST_UNARY_NOT:
                self.write("not ")
            elif expression.unary_operation.type == AST_UNARY_OPERATION.AST_UNARY_LENGTH:
                self.write("#")

            self.write_expression(expression.unary_operation.operand, parentheses)

        else:
            self.write("nil")

        if use_parentheses:
            self.write(")")

    def write_prefix_expression(self, expression: Expression, is_line_start: bool) -> None:
        if expression.type == AST_EXPRESSION.AST_EXPRESSION_VARIABLE:
            self.write_variable(expression.variable, is_line_start)
        elif expression.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL:
            self.write_function_call(expression.function_call, is_line_start)
        else:
            if is_line_start:
                self.write(";")
            self.write_expression(expression, True)

    def _format_slot_name(self, slot: int) -> str:
        return format_generated_name(
            self.format_slot,
            self.current_function_name_key,
            slot,
            "slot",
            self.file_path,
            "Lua::_format_slot_name",
        )

    def write_variable(self, variable: AstVariable, is_line_start: bool) -> None:
        if variable.type in (AST_VARIABLE.AST_VARIABLE_SLOT, AST_VARIABLE.AST_VARIABLE_UPVALUE):
            if variable.slot_scope is None or not variable.slot_scope.scope.name:
                self.write(self._format_slot_name(variable.slot))
            else:
                self.write(variable.slot_scope.scope.name)
            return
        if variable.type == AST_VARIABLE.AST_VARIABLE_GLOBAL:
            self.write(variable.name)
            return
        if variable.type == AST_VARIABLE.AST_VARIABLE_TABLE_INDEX:
            self.write_prefix_expression(variable.table, is_line_start)
            if variable.table_index is None:
                # Defensive fallback for unresolved multres table index forms.
                self.write("[", str(variable.multres_index), "]")
                return
            if (
                variable.table_index.type == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
                and variable.table_index.constant.is_name
            ):
                self.write(".", variable.table_index.constant.string)
            else:
                self.write("[")
                self.write_expression(variable.table_index, False)
                self.write("]")

    def write_function_call(self, function_call: AstFunctionCall, is_line_start: bool) -> None:
        if (
            function_call.is_method
            and function_call.function.variable is not None
            and function_call.function.variable.table is not None
            and function_call.function.variable.table_index is not None
            and function_call.function.variable.table_index.type
            == AST_EXPRESSION.AST_EXPRESSION_CONSTANT
        ):
            self.write_prefix_expression(function_call.function.variable.table, is_line_start)
            self.write(":", function_call.function.variable.table_index.constant.string)
        else:
            self.write_prefix_expression(function_call.function, is_line_start)
        self.write("(")
        self.write_expression_list(function_call.arguments, function_call.multres_argument)
        self.write(")")

    def write_assignment(
        self,
        variables: list[AstVariable],
        expressions: list[Expression],
        separator: str,
        is_line_start: bool,
    ) -> None:
        for i, var in enumerate(variables):
            self.write_variable(var, is_line_start if i == 0 else False)
            if i != len(variables) - 1:
                self.write(", ")
        if not expressions:
            return
        self.write(separator)
        for i, expr in enumerate(expressions):
            if i != len(expressions) - 1:
                self.write_expression(expr, False)
                self.write(", ")
                continue

            if len(expressions) != len(variables):
                if (
                    expr.type == AST_EXPRESSION.AST_EXPRESSION_VARARG
                    and expr.return_count == 1
                ):
                    self.write_expression(expr, True)
                    continue
                if (
                    expr.type == AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL
                    and expr.function_call.return_count == 1
                ):
                    self.write_expression(expr, True)
                    continue

            self.write_expression(expr, False)

    def write_expression_list(
        self,
        expressions: list[Expression],
        multres: Optional[Expression],
    ) -> None:
        for i, expr in enumerate(expressions):
            if i != len(expressions) - 1 or multres is not None:
                self.write_expression(expr, False)
                self.write(", ")
                continue

            if expr.type in (
                AST_EXPRESSION.AST_EXPRESSION_VARARG,
                AST_EXPRESSION.AST_EXPRESSION_FUNCTION_CALL,
            ):
                self.write_expression(expr, True)
                continue

            self.write_expression(expr, False)
        if multres is not None:
            self.write_expression(multres, False)

    def write_function_definition(self, function: Function, is_method: bool) -> None:
        self.write("(")
        start = 1 if is_method else 0
        for i in range(start, len(function.parameter_names)):
            self.write(function.parameter_names[i])
            if i != len(function.parameter_names) - 1 or function.is_variadic:
                self.write(", ")
        if function.is_variadic:
            self.write("...")
        self.write(")", self.NEW_LINE)
        self.indent_level += 1
        if function.block:
            self.write_block(function, function.block)
        else:
            self.write_indent()
            self.write("return", self.NEW_LINE)
        self.indent_level -= 1
        self.write_indent()
        self.write("end")
        self.prototype_data_left -= function.prototype.prototype_size
        print_progress_bar(
            self.bytecode.prototypes_total_size - self.prototype_data_left,
            self.bytecode.prototypes_total_size,
        )

    @staticmethod
    def _try_string_to_number(string: str, number: float) -> bool:
        try:
            return float(string) == number
        except Exception:
            return False

    def write_number(self, number: float) -> None:
        raw = bitcast_f64_to_u64(number)
        if (raw & DOUBLE_EXPONENT) == DOUBLE_SPECIAL:
            self.write("-1e309" if (raw & DOUBLE_SIGN) else "1e309")
            return

        s = format(number, ".15g")
        if not self._try_string_to_number(s, number):
            s = format(number, ".16g")
            if not self._try_string_to_number(s, number):
                s = format(number, ".17g")
                decompiler_assert(
                    self._try_string_to_number(s, number),
                    "Failed to convert number to valid string",
                    self.file_path,
                    "Lua::write_number",
                    __file__,
                    0,
                )

        self.write(s)

    def write_string(self, string: str) -> None:
        bytes_list = string.encode("latin-1")
        bulk_safe = self.unrestricted_ascii or bytes_list.isascii()
        if not bulk_safe:
            try:
                # CPython's decoder checks overlong sequences, surrogates,
                # continuation bytes, and the Unicode upper bound in C.
                bytes_list.decode("utf-8")
            except UnicodeDecodeError:
                pass
            else:
                bulk_safe = _UTF8_C1_CONTROL.search(bytes_list) is None
        if bulk_safe:
            self.write_buffer.append(
                string.translate(_LUA_STRING_ESCAPES)
                if _LUA_STRING_NEEDS_ESCAPE.search(bytes_list)
                else string
            )
            return

        n = len(bytes_list)
        i = 0
        parts: list[str] = []
        _chr = chr
        unrestricted = self.unrestricted_ascii

        while i < n:
            value = bytes_list[i]

            if unrestricted or not (value & 0x80):
                if (0x20 <= value <= 0x7E) or (unrestricted and value >= 0x80):
                    if value == 34 or value == 92:  # '"' or '\\'
                        parts.append("\\")
                    parts.append(_chr(value))
                    i += 1
                    continue

                if value == 0x07:
                    parts.append("\\a"); i += 1; continue
                if value == 0x08:
                    parts.append("\\b"); i += 1; continue
                if value == 0x09:
                    parts.append("\\t"); i += 1; continue
                if value == 0x0A:
                    parts.append("\\n"); i += 1; continue
                if value == 0x0B:
                    parts.append("\\v"); i += 1; continue
                if value == 0x0C:
                    parts.append("\\f"); i += 1; continue
                if value == 0x0D:
                    parts.append("\\r"); i += 1; continue

            elif (value & 0xE0) == 0xC0:
                if i + 1 < n:
                    b1 = bytes_list[i + 1]
                    utf16 = (value << 8) | b1
                    if (utf16 & 0xC0) == 0x80 and 0xC2A0 <= utf16 <= 0xDFBF:
                        parts.append(_chr(value))
                        parts.append(_chr(b1))
                        i += 2
                        continue

            elif (value & 0xF0) == 0xE0:
                if i + 2 < n:
                    b1 = bytes_list[i + 1]
                    b2 = bytes_list[i + 2]
                    utf24 = (value << 16) | (b1 << 8) | b2
                    if (utf24 & 0xC0C0) == 0x8080 and (
                        (0xE0A080 <= utf24 < 0xEDA080)
                        or (0xEDBFBF < utf24 <= 0xEFBFBF)
                    ):
                        parts.append(_chr(value))
                        parts.append(_chr(b1))
                        parts.append(_chr(b2))
                        i += 3
                        continue

            elif (value & 0xF8) == 0xF0:
                if i + 3 < n:
                    b1 = bytes_list[i + 1]
                    b2 = bytes_list[i + 2]
                    b3 = bytes_list[i + 3]
                    utf32 = (value << 24) | (b1 << 16) | (b2 << 8) | b3
                    if (
                        (utf32 & 0xC0C0C0) == 0x808080
                        and 0xF0908080 <= utf32 <= 0xF48FBFBF
                    ):
                        parts.append(_chr(value))
                        parts.append(_chr(b1))
                        parts.append(_chr(b2))
                        parts.append(_chr(b3))
                        i += 4
                        continue

            parts.append(f"\\x{value:02X}")
            i += 1

        # Keep one fragment per string instead of retaining every character in
        # the complete output buffer. The emitted bytes are unchanged.
        self.write_buffer.append("".join(parts))

    @staticmethod
    def get_operator_precedence(expression: Optional[Expression]) -> int:
        if expression is None:
            return 8

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_BINARY_OPERATION:
            t = expression.binary_operation.type
            if t == AST_BINARY_OPERATION.AST_BINARY_EXPONENTATION:
                return 7
            if t in (
                AST_BINARY_OPERATION.AST_BINARY_MULTIPLICATION,
                AST_BINARY_OPERATION.AST_BINARY_DIVISION,
                AST_BINARY_OPERATION.AST_BINARY_MODULO,
            ):
                return 5
            if t in (
                AST_BINARY_OPERATION.AST_BINARY_ADDITION,
                AST_BINARY_OPERATION.AST_BINARY_SUBTRACTION,
            ):
                return 4
            if t == AST_BINARY_OPERATION.AST_BINARY_CONCATENATION:
                return 3
            if t in (
                AST_BINARY_OPERATION.AST_BINARY_LESS_THAN,
                AST_BINARY_OPERATION.AST_BINARY_LESS_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_GREATER_THEN,
                AST_BINARY_OPERATION.AST_BINARY_GREATER_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_EQUAL,
                AST_BINARY_OPERATION.AST_BINARY_NOT_EQUAL,
            ):
                return 2
            if t == AST_BINARY_OPERATION.AST_BINARY_AND:
                return 1
            if t == AST_BINARY_OPERATION.AST_BINARY_OR:
                return 0

        if expression.type == AST_EXPRESSION.AST_EXPRESSION_UNARY_OPERATION:
            return 6

        return 8

    def write(self, *parts: str) -> None:
        self.write_buffer.extend(parts)

    def write_indent(self) -> None:
        self.write("\t" * self.indent_level)

    def write_file(self) -> None:
        path = Path(self.file_path)
        if path.exists() and not self.force_overwrite:
            raise DecompilerError("File already exists", self.file_path, "Lua::write_file")
        path.parent.mkdir(parents=True, exist_ok=True)
        output_text = "".join(self.write_buffer)
        output_text = self._postprocess_output(output_text)
        path.write_bytes(output_text.encode("latin1"))

    def _postprocess_output(self, text: str) -> str:
        # Both normalization patterns require this exact literal. Most chunks
        # cannot match, so avoid scanning them twice with the regular expressions.
        if "assert(io.open(" not in text:
            return text

        # Normalize a common split-path + open-file sequence into a single path local
        # while preserving stable generated names.
        pattern = re.compile(
            r"(?P<indent>\t*)local (?P<a>var_\d+_\d+) = (?P<aexpr>[^\r\n]+)\r\n"
            r"(?P=indent)local (?P<b>var_\d+_\d+) = (?P<bexpr>[^\r\n]+)\r\n"
            r"(?P=indent)local (?P<c>var_\d+_\d+) = assert\(io\.open\((?P<openexpr>[^\r\n]+), \"w\"\)\)\r\n"
            r"\r\n"
            r"(?P=indent)(?P<x>var_\d+_\d+) = (?P=c)\r\n"
            r"(?P=indent)(?P<y>var_\d+_\d+) = (?P=c)\.write"
        )

        def replace_match(match: re.Match[str]) -> str:
            indent = match.group("indent")
            var_a = match.group("a")
            var_b = match.group("b")
            var_x = match.group("x")
            var_y = match.group("y")
            aexpr = match.group("aexpr")
            bexpr = match.group("bexpr")
            openexpr = match.group("openexpr")

            prefix = f"{var_a} .. {var_b} .. "
            if not openexpr.startswith(prefix):
                return match.group(0)

            tail = openexpr[len(prefix) :]
            return (
                f"{indent}local {var_a} = {aexpr} .. {bexpr} .. {tail}\r\n"
                f"{indent}local {var_b} = assert(io.open({var_a}, \"w\"))\r\n"
                "\r\n"
                f"{indent}{var_x} = {var_b}\r\n"
                f"{indent}{var_y} = {var_b}.write"
            )

        text = pattern.sub(replace_match, text)

        function_rename_pattern = re.compile(
            r"(?P<section>"
            r"(?P<indent>\t*)local (?P<openvar>var_(?P<key>\d+)_(?P<openidx>\d+)) = assert\(io\.open\(var_\d+_\d+, \"w\"\)\)\r\n"
            r"\r\n"
            r"(?P=indent)var_\d+_\d+ = (?P=openvar)\r\n"
            r"(?P=indent)var_\d+_\d+ = (?P=openvar)\.write\r\n"
            r"[\s\S]*?"
            r"(?P<funcindent>\t*)local function (?P<func>var_(?P=key)_(?P<funcidx>\d+))\([^\r\n]*\)\r\n"
            r"[\s\S]*?"
            r"(?P<callindent>\t+)(?P=func)\()"
        )

        def replace_function_name(match: re.Match[str]) -> str:
            open_index = int(match.group("openidx"))
            function_index = int(match.group("funcidx"))
            if function_index != open_index + 2:
                return match.group("section")

            old_name = match.group("func")
            new_name = f"var_{match.group('key')}_{open_index + 1}"
            return match.group("section").replace(old_name, new_name)

        return function_rename_pattern.sub(replace_function_name, text)

def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="luajit-decompiler.py",
        description="Decompile LuaJIT bytecode into readable Lua source.",
    )
    parser.add_argument("input_path", help="Input .luac file or directory")
    parser.add_argument("-o", "--output", dest="output_path", default="", help="Output path")
    parser.add_argument(
        "-e", "--extension", dest="extension_filter", default="", help="Extension filter"
    )
    parser.add_argument("-s", "--silent_assertions", action="store_true")
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="Verbose logging: print detailed pipeline/instruction activity.",
    )
    parser.add_argument("-f", "--force_overwrite", action="store_true")
    parser.add_argument("-i", "--ignore_debug_info", action="store_true")
    parser.add_argument("-m", "--minimize_diffs", action="store_true")
    parser.add_argument("-u", "--unrestricted_ascii", action="store_true")
    parser.add_argument(
        "--backend",
        choices=["python"],
        default="python",
        help="Decompiler backend (python-only).",
    )
    parser.add_argument(
        "--validate-bytecode",
        action="store_true",
        help="Always parse bytecode in Python before decompiling.",
    )
    parser.add_argument(
        "--fail-on-unsupported-statements",
        action="store_true",
        help="Python backend: fail instead of emitting '-- unsupported statement'.",
    )
    parser.add_argument(
        "--format-arg",
        default=DEFAULT_FORMAT_ARG,
        help="Generated argument name format (supports one/two %%s placeholders).",
    )
    parser.add_argument(
        "--format-label",
        default=DEFAULT_FORMAT_LABEL,
        help="Generated label name format (supports one/two %%s placeholders).",
    )
    parser.add_argument(
        "--format-iter",
        default=DEFAULT_FORMAT_ITER,
        help="Generated iterator name format (supports one/two %%s placeholders).",
    )
    parser.add_argument(
        "--format-var",
        default=DEFAULT_FORMAT_VAR,
        help="Generated variable name format (supports one/two %%s placeholders).",
    )
    parser.add_argument(
        "--format-slot",
        default=DEFAULT_FORMAT_SLOT,
        help="Generated fallback slot name format (supports one/two %%s placeholders).",
    )
    parser.add_argument(
        "--decompress-tables",
        action="store_true",
        help="Expand default/metatable-compressed table rows when the pattern is recognized.",
    )
    parser.add_argument(
        "--decompress-tables-aggressive",
        action="store_true",
        help=(
            "Decompress tables and aggressively remove recognized metatable/default-table "
            "scaffolding that becomes unused."
        ),
    )
    parser.add_argument(
        "-w",
        "--workers",
        type=int,
        default=1,
        help=(
            "Number of parallel worker processes for batch decompilation. "
            "Default 1 (sequential). Values > 1 use multiprocessing for speedup."
        ),
    )
    return parser.parse_args(argv)


def _find_files(input_path: Path, extension_filter: str) -> list[Path]:
    if input_path.is_file():
        return [input_path]
    files: list[Path] = []
    ext = extension_filter.lower()
    if ext and not ext.startswith("."):
        ext = "." + ext
    for p in input_path.rglob("*"):
        if not p.is_file():
            continue
        if ext and p.suffix.lower() != ext:
            continue
        files.append(p)
    return files


def _default_output_dir() -> Path:
    return Path(__file__).resolve().parent / "output"


def _normalize_output_dir(path: str) -> Path:
    if path:
        out = Path(path)
    else:
        out = _default_output_dir()
    out.mkdir(parents=True, exist_ok=True)
    return out


def _validate_bytecode(files: Iterable[Path]) -> None:
    for file in files:
        bc = Bytecode(str(file))
        bc()
    erase_progress_bar()


def _decompile_single_file(
    file: Path,
    input_root: Path,
    output_root: Path,
    force_overwrite: bool,
    ignore_debug_info: bool,
    minimize_diffs: bool,
    unrestricted_ascii: bool,
    fail_on_unsupported_statements: bool,
    format_arg: str,
    format_label: str,
    format_iter: str,
    format_var: str,
    format_slot: str,
    decompress_tables: bool,
    decompress_tables_aggressive: bool,
    quiet: bool = False,
) -> None:
    """Decompile a single .luac file. Used both sequentially and as a worker."""
    relative = file.relative_to(input_root)
    output_file = (output_root / relative).with_suffix(".lua")
    if not quiet:
        verbose_push(f"Decompile file: {file}")
    try:
        if not quiet:
            verbose_log(f"Output file: {output_file}")
            print_line(f"Input file: {file}")
            print_line("Reading bytecode...")
        bytecode = Bytecode(str(file))
        bytecode()
        if not quiet:
            print_line("Building ast...")
        ast = Ast(
            bytecode,
            ignore_debug_info,
            minimize_diffs,
            format_arg=format_arg,
            format_label=format_label,
            format_iter=format_iter,
            format_var=format_var,
        )
        ast()
        if decompress_tables or decompress_tables_aggressive:
            if not quiet:
                verbose_log(
                    "Apply table decompression pass"
                    + (" (aggressive)" if decompress_tables_aggressive else "")
                )
            ast.decompress_tables(aggressive=decompress_tables_aggressive)
        if not quiet:
            print_line("Writing lua source...")
        lua = Lua(
            bytecode,
            ast,
            str(output_file),
            force_overwrite=force_overwrite,
            minimize_diffs=minimize_diffs,
            unrestricted_ascii=unrestricted_ascii,
            fail_on_unsupported_statements=fail_on_unsupported_statements,
            format_slot=format_slot,
        )
        lua()
        if not quiet:
            print_line(f"Output file: {output_file}")
    finally:
        if not quiet:
            verbose_pop("Decompile done")


def _worker_decompile(args: tuple) -> tuple[str, bool, str]:
    """Top-level worker for ProcessPoolExecutor. Returns (filename, success, error_msg)."""
    (
        file_str, input_root_str, output_root_str,
        force_overwrite, ignore_debug_info, minimize_diffs,
        unrestricted_ascii, fail_on_unsupported_statements,
        format_arg, format_label, format_iter, format_var, format_slot,
        decompress_tables, decompress_tables_aggressive,
    ) = args
    file = Path(file_str)
    input_root = Path(input_root_str)
    output_root = Path(output_root_str)
    try:
        _decompile_single_file(
            file, input_root, output_root,
            force_overwrite, ignore_debug_info, minimize_diffs,
            unrestricted_ascii, fail_on_unsupported_statements,
            format_arg, format_label, format_iter, format_var, format_slot,
            decompress_tables, decompress_tables_aggressive,
            quiet=True,
        )
        return (file_str, True, "")
    except Exception as exc:
        return (file_str, False, str(exc))


def _decompile_with_python_backend(
    files: list[Path],
    input_root: Path,
    output_root: Path,
    force_overwrite: bool,
    ignore_debug_info: bool,
    minimize_diffs: bool,
    unrestricted_ascii: bool,
    fail_on_unsupported_statements: bool,
    format_arg: str,
    format_label: str,
    format_iter: str,
    format_var: str,
    format_slot: str,
    decompress_tables: bool,
    decompress_tables_aggressive: bool,
    num_workers: int = 1,
) -> None:
    if num_workers <= 1:
        # Sequential (original behavior)
        for file in files:
            _decompile_single_file(
                file, input_root, output_root,
                force_overwrite, ignore_debug_info, minimize_diffs,
                unrestricted_ascii, fail_on_unsupported_statements,
                format_arg, format_label, format_iter, format_var, format_slot,
                decompress_tables, decompress_tables_aggressive,
            )
        return

    # Parallel using multiprocessing
    print_line(f"Decompiling {len(files)} file(s) with {num_workers} worker processes...")
    work_items = [
        (
            str(f), str(input_root), str(output_root),
            force_overwrite, ignore_debug_info, minimize_diffs,
            unrestricted_ascii, fail_on_unsupported_statements,
            format_arg, format_label, format_iter, format_var, format_slot,
            decompress_tables, decompress_tables_aggressive,
        )
        for f in files
    ]

    completed = 0
    failed: list[tuple[str, str]] = []
    total = len(files)

    with concurrent.futures.ProcessPoolExecutor(max_workers=num_workers) as pool:
        futures = {pool.submit(_worker_decompile, item): item[0] for item in work_items}
        for future in concurrent.futures.as_completed(futures):
            file_str, success, error_msg = future.result()
            completed += 1
            rel_name = Path(file_str).name
            if success:
                sys.stdout.write(f"\r[{completed}/{total}] {rel_name}" + " " * 20)
                sys.stdout.flush()
            else:
                failed.append((file_str, error_msg))
                sys.stdout.write(f"\r[{completed}/{total}] FAILED: {rel_name}" + " " * 20)
                sys.stdout.flush()

    sys.stdout.write("\n")
    sys.stdout.flush()

    if failed:
        print_line(f"\n{len(failed)} file(s) failed:")
        for fpath, err in failed:
            print_line(f"  {fpath}: {err}")
        raise DecompilerError(f"Failed to decompile {len(failed)} of {total} files.")
    else:
        print_line(f"All {total} file(s) decompiled successfully.")


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    set_verbose(args.verbose)
    if args.verbose:
        verbose_log(
            "CLI options: "
            f"backend={args.backend}, minimize_diffs={args.minimize_diffs}, "
            f"ignore_debug_info={args.ignore_debug_info}, validate_bytecode={args.validate_bytecode}, "
            f"decompress_tables={args.decompress_tables}, "
            f"decompress_tables_aggressive={args.decompress_tables_aggressive}, "
            f"fail_on_unsupported_statements={args.fail_on_unsupported_statements}"
        )
    input_path = Path(args.input_path).resolve()
    if not input_path.exists():
        print_line(f"Failed to open input path: {input_path}")
        return 1

    input_root = input_path if input_path.is_dir() else input_path.parent
    output_root = _normalize_output_dir(args.output_path)
    files = _find_files(input_path, args.extension_filter)

    if not files:
        if input_path.is_dir():
            ext = args.extension_filter
            if ext and not ext.startswith("."):
                ext = "." + ext
            print_line(
                f"No files {'with extension ' + ext + ' ' if ext else ''}found in path: {input_path}"
            )
        else:
            print_line(f"Failed to open input path: {input_path}")
        return 1

    print_line(PROGRAM_NAME)
    if args.verbose:
        verbose_log(f"Resolved input root: {input_root}")
        verbose_log(f"Resolved output root: {output_root}")
        verbose_log(f"Matched {len(files)} input file(s)")
    try:
        if args.validate_bytecode:
            _validate_bytecode(files)

        _decompile_with_python_backend(
            files,
            input_root,
            output_root,
            force_overwrite=args.force_overwrite,
            ignore_debug_info=args.ignore_debug_info,
            minimize_diffs=args.minimize_diffs,
            unrestricted_ascii=args.unrestricted_ascii,
            fail_on_unsupported_statements=args.fail_on_unsupported_statements,
            format_arg=args.format_arg,
            format_label=args.format_label,
            format_iter=args.format_iter,
            format_var=args.format_var,
            format_slot=args.format_slot,
            decompress_tables=args.decompress_tables,
            decompress_tables_aggressive=args.decompress_tables_aggressive,
            num_workers=args.workers,
        )

        print_line("Done!")
        return 0
    except DecompilerError as exc:
        erase_progress_bar()
        print_line(str(exc))
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
