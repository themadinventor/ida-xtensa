#
# IDAPython Xtensa processor module
# https://github.com/themadinventor/ida-xtensa
#
# Copyright (C) 2014 Fredrik Ahlberg
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
# Street, Fifth Floor, Boston, MA 02110-1301 USA.

#  v0.1 - changes by tinhead
#  bug fix for 'l8ui','l16si','l16ui','l32i','s8i','s16i' and 's32i' size and shift
#  bug fix for 'rsr.epc2','rsr.epc3' detection
#  'ill' added, normally one can work without
#  'rsr.epc4','rsr.epc5','rsr.epc6','rsr.epc7' added
#
#  v0.2 - changes by tinhead
#  bug fix for 'addmi' size
#  bug fix for 'movi' size
#  bug fix for 'l32r' with offset >= 0
#  note: movi.n and addi with values higher than 127 looks bit wired in compare to
#        xt-objdump, better would be something like 'ret.value = 0x80 - ret.value'

import copy

try:
    from idaapi import *
except ImportError:
    class processor_t(object):
        pass
    dt_byte = dt_word = dt_dword = None
    PR_SEGS = PR_DEFSEG32 = PR_RNAMESOK = PR_ADJSEGS = PRN_HEX = PR_USE32 = 0
    ASH_HEXF3 = ASD_DECF0 = ASO_OCTF1 = ASB_BINF3 = AS_NOTAB = AS_ASCIIC = AS_ASCIIZ = 0
    CF_CALL = CF_JUMP = CF_STOP = 0
    o_void = o_reg = o_imm = o_displ = o_near = None

class Operand:
    REG     = 0
    IMM     = 1
    MEM     = 2
    RELA    = 3
    RELAL   = 4
    RELU    = 5
    MEM_INDEX = 6

    def __init__(self, type, size, rshift, size2 = 0, rshift2 = 0, signext = False, vshift = 0, off = 0, xlate = None, dt = dt_byte, regbase = None):
        self.type = type
        self.size = size
        self.rshift = rshift
        self.size2 = size2
        self.rshift2 = rshift2
        self.signext = signext or (self.type in (Operand.RELA, Operand.RELAL, Operand.MEM))
        self.vshift = vshift
        self.off = off
        self.xlate = xlate
        self.dt = dt
        self.regbase = regbase


    def bitfield(self, op, size, rshift):
        val = (op >> rshift) & (0xffffffff >> (32 - size))
        return val

    def parse(self, ret, op, cmd = None):
        val = self.bitfield(op, self.size, self.rshift)
        if self.size2:
            val |= ((op >> self.rshift2) & (0xffffffff >> (32-self.size2))) << self.size

        if self.signext and (val & (1 << (self.size+self.size2-1))):
            val = -((~val)&((1 << (self.size+self.size2-1))-1))-1

        val <<= self.vshift
        val += self.off

        if self.xlate:
            val = self.xlate(val)

        ret.dtyp = self.dt
        if self.type == Operand.REG:
            ret.type = o_reg
            ret.reg = val if val < 16 else 16
        elif self.type == Operand.IMM:
            ret.type = o_imm
            ret.value = val
        elif self.type == Operand.MEM:
            ret.type = o_mem
            ret.addr = (cmd.ea+3+(val<<2))&0xfffffffc if val < 0 else (((cmd.ea+3+(val<<2))-0x40000)&0xfffffffc)
        elif self.type == Operand.MEM_INDEX:
            ret.type = o_displ
            ret.phrase = self.bitfield(op, *self.regbase)
            ret.addr = val
        elif self.type in (Operand.RELA, Operand.RELAL):
            ret.type = o_near
            ret.addr = val + cmd.ea + 4 if self.type == Operand.RELA else ((cmd.ea&0xfffffffc)+4+(val<<2))
        elif self.type == Operand.RELU:
            ret.type = o_near
            ret.addr = val + cmd.ea + 4
        else:
            raise ValueError("unhandled operand type");

# These magic lookup tables are defined in table 3-17 and 3-18 (p.41-42) in
# Xtensa Instruction Set Architecture Reference Manual
def b4const(val):
    lut = (-1, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 16, 32, 64, 128, 256)
    return lut[val]

def b4constu(val):
    lut = (32768, 65536, 2, 3, 4, 5, 6, 7, 8, 10, 12, 16, 32, 64, 128, 256)
    return lut[val]

def movi_n(val):
    return val if val & 0x60 != 0x60 else -(0x20 - val & 0x1f)

def addin(val):
    return val if val else -1

def shimm(val):
    return 32-val

class Instr(object):

    fmt_NONE        = (3, ())
    fmt_NNONE       = (2, ())
    fmt_NNNONE      = (1, ())
    fmt_RRR         = (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.REG, 4, 4)))
    fmt_RRR_ceil    = (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4)))
    fmt_RRR_extui   = (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8, 1, 16), Operand(Operand.IMM, 4, 20, off=1)))
    fmt_RRR_sext    = (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, off=7)))
    fmt_RRR_1imm    = (3, (Operand(Operand.IMM, 4, 8),))
    fmt_RRR_2imm    = (3, (Operand(Operand.IMM, 4, 8), Operand(Operand.IMM, 4, 4)))
    fmt_RRR_lddec   = (3, (Operand(Operand.IMM, 4, 8), Operand(Operand.IMM, 2, 12)))
    fmt_RRR_immr    = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8)))
    fmt_RRR_2r      = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8)))
    fmt_RRR_2rr     = (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4)))
    fmt_RRR_sll     = (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8)))
    fmt_RRR_slli    = (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, 1, 20, xlate=shimm)))
    fmt_RRR_srai    = (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8, 1, 20)))
    fmt_RRR_sh      = (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8)))
    fmt_RRR_ssa     = (3, (Operand(Operand.REG, 4, 8),))
    fmt_RRR_mul_ad  = (3, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 1, 6)))
    fmt_RRR_mul_da  = (3, (Operand(Operand.IMM, 1, 14), Operand(Operand.REG, 4, 4)))
    fmt_RRR_mul_dd  = (3, (Operand(Operand.IMM, 1, 14), Operand(Operand.IMM, 1, 6)))
    fmt_RRR_ssai    = (3, (Operand(Operand.IMM, 4, 8, 1, 4),))
    fmt_RRI4        = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 12, 4)))
    fmt_RRI8        = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 8, 16, signext = True)))
    fmt_RRI8_lsi    = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 8, 16)))
    fmt_RRI8_bf     = (3, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 8, 16,)))
    fmt_RRI8_loop   = (3, (Operand(Operand.REG, 4, 8), Operand(Operand.RELU, 8, 16)))
    fmt_RRI8_addmi  = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 8, 16, signext = True, vshift=8, dt=dt_dword)))
    fmt_RRI8_i12    = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 8, 16, 4, 8, dt=dt_word)))
    fmt_RRI8_disp   = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 8, 16, vshift=0, regbase=(4, 8))))
    fmt_RRI8_disp16 = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 8, 16, vshift=1, dt=dt_word, regbase=(4, 8))))
    fmt_RRI8_disp32 = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 8, 16, vshift=2, dt=dt_dword, regbase=(4, 8))))
    fmt_RRI8_l32ai  = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8), Operand(Operand.MEM_INDEX, 8, 16, vshift=2, dt=dt_dword, regbase=(4, 8))))
    fmt_RRI8_s32c1a = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 8, 16)))
    fmt_RRI8_b      = (3, (Operand(Operand.REG, 4, 8), Operand(Operand.REG, 4, 4), Operand(Operand.RELA, 8, 16)))
    fmt_RRI8_bb     = (3, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, 1, 12), Operand(Operand.RELA, 8, 16)))
    fmt_RI16        = (3, (Operand(Operand.REG, 4, 4), Operand(Operand.MEM, 16, 8, dt=dt_dword)))
    fmt_BRI8        = (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.RELA, 8, 16)))
    fmt_BRI8_imm    = (3, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 12, xlate = b4const), Operand(Operand.RELA, 8, 16)))
    fmt_BRI8_immu   = (3, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 12, xlate = b4constu), Operand(Operand.RELA, 8, 16)))
    fmt_BRI12       = (3, (Operand(Operand.REG, 4, 8), Operand(Operand.RELA, 12, 12)))
    fmt_RI12S3      = (3, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 12, 12, vshift=3)))
    fmt_CALL        = (3, (Operand(Operand.RELA, 18, 6),))
    fmt_CALL_sh     = (3, (Operand(Operand.RELAL, 18, 6),))
    fmt_CALLX       = (3, (Operand(Operand.REG, 4, 8),))
    fmt_RSR         = (3, (Operand(Operand.IMM, 8, 8), Operand(Operand.REG, 4, 4)))
    fmt_RSR_spec    = (3, (Operand(Operand.REG, 4, 4),))
    fmt_RRRN        = (2, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.REG, 4, 4)))
    fmt_RRRN_addi   = (2, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, xlate=addin)))
    fmt_RRRN_2r     = (2, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8)))
    fmt_RRRN_disp   = (2, (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 4, 12, vshift=2, regbase=(4, 8))))
    fmt_RI6         = (2, (Operand(Operand.REG, 4, 8), Operand(Operand.RELU, 4, 12, 2, 4)))
    fmt_RI7         = (2, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 12, 3, 4, xlate=movi_n)))

    def __init__(self, name, opcode, mask, fmt, flags = 0):
        self.name = name
        self.opcode = opcode
        self.mask = mask
        (self.size, self.fmt) = fmt
        self.flags = flags

    def match(self, op):
        return (op & self.mask) == self.opcode

    def parseOperands(self, operands, op, cmd = None):
        for ret, fmt in zip(operands, self.fmt):
            fmt.parse(ret, op, cmd)

    def __str__(self):
        return "<Instr %s %x/%x>" % (self.name, self.opcode, self.mask)

class XtensaProcessor(processor_t):
    id = 0x8000 + 1990
    flag = PR_SEGS | PR_DEFSEG32 | PR_RNAMESOK | PR_ADJSEGS | PRN_HEX | PR_USE32
    cnbits = 8
    dnbits = 8
    psnames = ["xtensa"]
    plnames = ["Tensilica Xtensa"]
    segreg_size = 0
    tbyte_size = 0

    instruc_start = 0

    assembler = {
        "flag": ASH_HEXF3 | ASD_DECF0 | ASO_OCTF1 | ASB_BINF3 | AS_NOTAB
            | AS_ASCIIC | AS_ASCIIZ,
        "uflag": 0,
        "name": "GNU assembler",
        "origin": ".org",
        "end": "end",
        "cmnt": ";",
        "ascsep": '"',
        "accsep": "'",
        "esccodes": "\"'",
        "a_ascii": ".ascii",
        "a_byte": ".byte",
        "a_word": ".short",
        "a_dword": ".int",
        "a_bss": "dfs %s",
        "a_seg": "seg",
        "a_curip": ".",
        "a_public": "",
        "a_weak": "",
        "a_extrn": ".extrn",
        "a_comdef": "",
        "a_align": ".align",
        "lbrace": "(",
        "rbrace": ")",
        "a_mod": "%",
        "a_band": "&",
        "a_bor": "|",
        "a_xor": "^",
        "a_bnot": "~",
        "a_shl": "<<",
        "a_shr": ">>",
        "a_sizeof_fmt": "size %s",
    }

    ops = (
        ("abs",    0x600100, 0xff0f0f, Instr.fmt_RRR_2rr ),
        ("abs.s",  0xfa0010, 0xff00ff, Instr.fmt_RRR_sll ),
        ("add",    0x800000, 0xff000f, Instr.fmt_RRR ),
        ("add.s",  0x0a0000, 0xff000f, Instr.fmt_RRR ),
        ("addi",   0x00c002, 0x00f00f, Instr.fmt_RRI8 ),
        ("addmi",  0x00d002, 0x00f00f, Instr.fmt_RRI8_addmi ),
        ("addx2",  0x900000, 0xff000f, Instr.fmt_RRR ),
        ("addx4",  0xa00000, 0xff000f, Instr.fmt_RRR ),
        ("addx8",  0xb00000, 0xff000f, Instr.fmt_RRR ),
        ("all4",   0x009000, 0xfff00f, Instr.fmt_RRR_2r ),
        ("all8",   0x00b000, 0xfff00f, Instr.fmt_RRR_2r ),
        ("and",    0x100000, 0xff000f, Instr.fmt_RRR ),
        ("andb",   0x020000, 0xff000f, Instr.fmt_RRR ),
        ("andbc",  0x120000, 0xff000f, Instr.fmt_RRR ),
        ("any4",   0x008000, 0xfff00f, Instr.fmt_RRR_2r ),
        ("any8",   0x00a000, 0xfff00f, Instr.fmt_RRR_2r ),
        ("ball",   0x004007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("bany",   0x008007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("bbc",    0x005007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("bbs",    0x00d007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("bbci",   0x006007, 0x00e00f, Instr.fmt_RRI8_bb, CF_JUMP ),
        ("bbsi",   0x00e007, 0x00e00f, Instr.fmt_RRI8_bb, CF_JUMP ),
        ("beq",    0x001007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("beqi",   0x000026, 0x0000ff, Instr.fmt_BRI8_imm, CF_JUMP ), # was RRI8
        ("beqz",   0x000016, 0x0000ff, Instr.fmt_BRI12, CF_JUMP ),
        ("bf",     0x000076, 0x00f0ff, Instr.fmt_RRI8_bf, CF_JUMP ),
        ("bge",    0x00a007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("bgei",   0x0000e6, 0x0000ff, Instr.fmt_BRI8_imm, CF_JUMP ),
        ("bgeu",   0x00b007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("bgeui",  0x0000f6, 0x0000ff, Instr.fmt_BRI8_immu, CF_JUMP ),
        ("bgez",   0x0000d6, 0x0000ff, Instr.fmt_BRI12, CF_JUMP ),
        ("blt",    0x002007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("blti",   0x0000a6, 0x0000ff, Instr.fmt_BRI8_imm, CF_JUMP ),
        ("bltu",   0x003007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("bltui",  0x0000b6, 0x0000ff, Instr.fmt_BRI8_immu, CF_JUMP ),
        ("bltz",   0x000096, 0x0000ff, Instr.fmt_BRI12, CF_JUMP ),
        ("bnall",  0x00c007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("bnone",  0x000007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("bne",    0x009007, 0x00f00f, Instr.fmt_RRI8_b, CF_JUMP ),
        ("bnei",   0x000066, 0x0000ff, Instr.fmt_BRI8_imm, CF_JUMP ),
        ("bnez",   0x000056, 0x0000ff, Instr.fmt_BRI12, CF_JUMP ),
        ("break",  0x004000, 0xfff00f, Instr.fmt_RRR_2imm ),
        ("bt",     0x001076, 0x00f0ff, Instr.fmt_RRI8_bf, CF_JUMP ),
        ("call0",  0x000005, 0x00003f, Instr.fmt_CALL_sh, CF_CALL | CF_JUMP),
        ("call4",  0x000015, 0x00003f, Instr.fmt_CALL_sh, CF_CALL | CF_JUMP),
        ("call8",  0x000025, 0x00003f, Instr.fmt_CALL_sh, CF_CALL | CF_JUMP),
        ("call12", 0x000035, 0x00003f, Instr.fmt_CALL_sh, CF_CALL | CF_JUMP),
        ("callx0", 0x0000c0, 0xfff0ff, Instr.fmt_CALLX, CF_CALL | CF_JUMP ),
        ("callx4", 0x0000d0, 0xfff0ff, Instr.fmt_CALLX, CF_CALL | CF_JUMP ),
        ("callx8", 0x0000e0, 0xfff0ff, Instr.fmt_CALLX, CF_CALL | CF_JUMP ),
        ("callx12",0x0000f0, 0xfff0ff, Instr.fmt_CALLX, CF_CALL | CF_JUMP ),
        ("ceil.s", 0xba0000, 0xff000f, Instr.fmt_RRR_ceil, ),
        ("clamps", 0x330000, 0xff000f, Instr.fmt_RRR_ceil, ),
        ("dsync",  0x002030, 0xffffff, Instr.fmt_NONE ),
        ("entry",  0x000036, 0x0000ff, Instr.fmt_RI12S3 ),
        ("esync",  0x002020, 0xffffff, Instr.fmt_NONE ),
        ("excw",   0x002080, 0xffffff, Instr.fmt_NONE ),
        ("extui",  0x040000, 0x0e000f, Instr.fmt_RRR_extui ),
        ("extw",   0x0020d0, 0xffffff, Instr.fmt_NONE ),
        ("float.s",0xca0000, 0xff000f, Instr.fmt_RRR_ceil ),
        ("floor.s",0xaa0000, 0xff000f, Instr.fmt_RRR_ceil ),
        ("isync",  0x002000, 0xffffff, Instr.fmt_NONE ),
        ("ill",    0x000000, 0xffffff, Instr.fmt_NONE ),
        ("j",      0x000006, 0x00003f, Instr.fmt_CALL, CF_STOP | CF_JUMP),
        ("jx",     0x0000a0, 0xfff0ff, Instr.fmt_CALLX, CF_STOP | CF_JUMP ),
        ("l8ui",   0x000002, 0x00f00f, Instr.fmt_RRI8_disp ),
        ("l16si",  0x009002, 0x00f00f, Instr.fmt_RRI8_disp16 ),
        ("l16ui",  0x001002, 0x00f00f, Instr.fmt_RRI8_disp16 ),
        ("l32ai",  0x00b002, 0x00f00f, Instr.fmt_RRI8_l32ai ),
        ("l32e",   0x090000, 0xff000f, Instr.fmt_RRR_ceil ),
        ("l32i",   0x002002, 0x00f00f, Instr.fmt_RRI8_disp32 ),
        ("l32r",   0x000001, 0x00000f, Instr.fmt_RI16 ),
        ("lddec",  0x900004, 0xffc0ff, Instr.fmt_RRR_lddec ),
        ("ldinc",  0x800004, 0xffc0ff, Instr.fmt_RRR_lddec ),
        ("loop",   0x008076, 0x00f0ff, Instr.fmt_RRI8_loop, CF_JUMP ),
        ("loopgtz",0x00a076, 0x00f0ff, Instr.fmt_RRI8_loop, CF_JUMP ),
        ("loopnez",0x009076, 0x00f0ff, Instr.fmt_RRI8_loop, CF_JUMP ),
        ("lsi",    0x000003, 0x00f00f, Instr.fmt_RRI8_lsi ),
        ("lsiu",   0x008003, 0x00f00f, Instr.fmt_RRI8_lsi ),
        ("lsx",    0x080000, 0xff000f, Instr.fmt_RRR ),
        ("lsxu",   0x180000, 0xff000f, Instr.fmt_RRR ),
        ("madd.s", 0x4a0000, 0xff000f, Instr.fmt_RRR ),
        ("max",    0x530000, 0xff000f, Instr.fmt_RRR ),
        ("maxu",   0x730000, 0xff000f, Instr.fmt_RRR ),
        ("memw",   0x0020c0, 0xffffff, Instr.fmt_NONE ),
        ("min",    0x430000, 0xff000f, Instr.fmt_RRR ),
        ("minu",   0x630000, 0xff000f, Instr.fmt_RRR ),
        ("mov",    0x200000, 0xff000f, Instr.fmt_RRR_sll ),
        ("mov.s",  0xfa0000, 0xff00ff, Instr.fmt_RRR_sll ),
        ("moveqz", 0x830000, 0xff000f, Instr.fmt_RRR ),
        ("moveqz.s",      0x8b0000, 0xff000f, Instr.fmt_RRR ),
        ("movf",   0xc30000, 0xff000f, Instr.fmt_RRR ),
        ("movf.s", 0xcb0000, 0xff000f, Instr.fmt_RRR ),
        ("movgez", 0xb30000, 0xff000f, Instr.fmt_RRR ),
        ("movgez.s",      0xbb0000, 0xff000f, Instr.fmt_RRR ),
        ("movi",   0x00a002, 0x00f00f, Instr.fmt_RRI8_i12 ),
        ("movltz", 0xa30000, 0xff000f, Instr.fmt_RRR ),
        ("movltz.s",      0xab0000, 0xff000f, Instr.fmt_RRR ),
        ("movnez", 0x930000, 0xff000f, Instr.fmt_RRR ),
        ("movnez.s",      0x9b0000, 0xff000f, Instr.fmt_RRR ),
        ("movsp",  0x001000, 0xfff00f, Instr.fmt_RRR_2r ),
        ("movt",   0xd30000, 0xff000f, Instr.fmt_RRR ),
        ("movt.s", 0xdb0000, 0xff000f, Instr.fmt_RRR ),
        ("msub.s", 0x5a0000, 0xff000f, Instr.fmt_RRR ),
        ("mul.aa.ll",     0x740004, 0xfff00f, Instr.fmt_RRR_2r ),
        ("mul.aa.hl",     0x750004, 0xfff00f, Instr.fmt_RRR_2r ),
        ("mul.aa.lh",     0x760004, 0xfff00f, Instr.fmt_RRR_2r ),
        ("mul.aa.hh",     0x770004, 0xfff00f, Instr.fmt_RRR_2r ),
        ("mul.ad.ll",     0x340004, 0xfff0bf, Instr.fmt_RRR_mul_ad ),
        ("mul.ad.hl",     0x350004, 0xfff0bf, Instr.fmt_RRR_mul_ad ),
        ("mul.ad.lh",     0x360004, 0xfff0bf, Instr.fmt_RRR_mul_ad ),
        ("mul.ad.hh",     0x370004, 0xfff0bf, Instr.fmt_RRR_mul_ad ),
        ("mul.da.ll",     0x640004, 0xffbf0f, Instr.fmt_RRR_mul_da ),
        ("mul.da.lh",     0x650004, 0xffbf0f, Instr.fmt_RRR_mul_da ),
        ("mul.da.hl",     0x650004, 0xffbf0f, Instr.fmt_RRR_mul_da ),
        ("mul.da.hh",     0x670004, 0xffbf0f, Instr.fmt_RRR_mul_da ),
        ("mul.dd.ll",     0x240004, 0xffbfbf, Instr.fmt_RRR_mul_dd ),
        ("mul.dd.lh",     0x250004, 0xffbfbf, Instr.fmt_RRR_mul_dd ),
        ("mul.dd.hl",     0x260004, 0xffbfbf, Instr.fmt_RRR_mul_dd ),
        ("mul.dd.hh",     0x270004, 0xffbfbf, Instr.fmt_RRR_mul_dd ),
        ("mul.s", 0x2a0000, 0xff000f, Instr.fmt_RRR ),
        ("mula.aa.ll",    0x780004, 0xfff00f, Instr.fmt_RRR_2r ),
        ("mula.aa.hl",    0x790004, 0xfff00f, Instr.fmt_RRR_2r ),
        ("mula.aa.lh",    0x7a0004, 0xfff00f, Instr.fmt_RRR_2r ),
        ("mula.aa.hh",    0x7b0004, 0xfff00f, Instr.fmt_RRR_2r ),
        ("mula.ad.ll",    0x380004, 0xfff0bf, Instr.fmt_RRR_mul_ad ),
        ("mula.ad.hl",    0x390004, 0xfff0bf, Instr.fmt_RRR_mul_ad ),
        ("mula.ad.lh",    0x3a0004, 0xfff0bf, Instr.fmt_RRR_mul_ad ),
        ("mula.ad.hh",    0x3b0004, 0xfff0bf, Instr.fmt_RRR_mul_ad ),
        ("mula.da.ll",    0x680004, 0xffbf0f, Instr.fmt_RRR_mul_da ),
        ("mula.da.lh",    0x690004, 0xffbf0f, Instr.fmt_RRR_mul_da ),
        ("mula.da.hl",    0x6a0004, 0xffbf0f, Instr.fmt_RRR_mul_da ),
        ("mula.da.hh",    0x6b0004, 0xffbf0f, Instr.fmt_RRR_mul_da ),
        ("mula.dd.ll",    0x280004, 0xffbfbf, Instr.fmt_RRR_mul_dd ),
        ("mula.dd.lh",    0x290004, 0xffbfbf, Instr.fmt_RRR_mul_dd ),
        ("mula.dd.hl",    0x2a0004, 0xffbfbf, Instr.fmt_RRR_mul_dd ),
        ("mula.dd.hh",    0x2b0004, 0xffbfbf, Instr.fmt_RRR_mul_dd ),
        ("mull",   0x820000, 0xff000f, Instr.fmt_RRR ),
        ("mulsh",  0xb10000, 0xff000f, Instr.fmt_RRR ),
        ("mul16s", 0xd10000, 0xff000f, Instr.fmt_RRR ),
        ("mul16u", 0xc10000, 0xff000f, Instr.fmt_RRR ),
        ("muluh",  0xa20000, 0xff000f, Instr.fmt_RRR ),
        ("neg",    0x600000, 0xff0f0f, Instr.fmt_RRR_2rr ),
        ("neg.s",  0xfa0060, 0xff00ff, Instr.fmt_RRR_sll ),
        ("nop",    0x0020f0, 0xffffff, Instr.fmt_NONE ),
        ("nsa",    0x40e000, 0xfff00f, Instr.fmt_RRR_2r ),
        ("nsau",   0x40f000, 0xfff00f, Instr.fmt_RRR_2r ),
        ("oeq.s",  0x2b0000, 0xff000f, Instr.fmt_RRR ),
        ("ole.s",  0x6b0000, 0xff000f, Instr.fmt_RRR ),
        ("olt.s",  0x4b0000, 0xff000f, Instr.fmt_RRR ),
        ("or",     0x200000, 0xff000f, Instr.fmt_RRR ),
        ("orb",    0x220000, 0xff000f, Instr.fmt_RRR ),
        ("orbc",   0x320000, 0xff000f, Instr.fmt_RRR ),
        ("quos",   0xd20000, 0xff000f, Instr.fmt_RRR ),
        ("quou",   0xc20000, 0xff000f, Instr.fmt_RRR ),
        ("rmes",   0xf20000, 0xff000f, Instr.fmt_RRR ),
        ("remu",   0xe20000, 0xff000f, Instr.fmt_RRR ),
        ("rer",    0x406000, 0xfff00f, Instr.fmt_RRR_2r ),
        ("ret",    0x000080, 0xffffff, Instr.fmt_NONE, CF_STOP ),
        ("retw",   0x000090, 0xffffff, Instr.fmt_NONE, CF_STOP ),
        ("rfr",    0xfa0040, 0xff00ff, Instr.fmt_RRR_sll ),
        ("rfue",   0x003100, 0xffffff, Instr.fmt_NONE, CF_STOP ),
        ("rfwo",   0x003400, 0xffffff, Instr.fmt_NONE, CF_STOP ),
        ("rfwu",   0x003500, 0xffffff, Instr.fmt_NONE, CF_STOP ),
        ("round.s",0x8a0000, 0xff000f, Instr.fmt_RRR_ceil ),
        ("rfe",    0x003000, 0xffffff, Instr.fmt_NONE, CF_STOP ),
        ("rfi",    0x003010, 0xfff0ff, Instr.fmt_RRR_1imm, CF_STOP ),
        ("rsr.prid",      0x03eb00, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.epc1",      0x03b100, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.epc2",      0x03b200, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.epc3",      0x03b300, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.epc4",      0x03b400, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.epc5",      0x03b500, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.epc6",      0x03b600, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.epc7",      0x03b700, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.ps",        0x03e600, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.exccause",  0x03e800, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.ccount",    0x03e400, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.excvaddr",  0x03ee00, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.depc",      0x03c000, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.prid",      0x03eb00, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.ccompare0", 0x03f000, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.interrupt", 0x03e200, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.intenable", 0x03e400, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.sar",       0x030300, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr.ddr",       0x036800, 0xffff0f, Instr.fmt_RSR_spec ),
        ("rsr",    0x030000, 0xff000f, Instr.fmt_RSR ),
        ("rsync",  0x002010, 0xffffff, Instr.fmt_NONE ),
        ("s8i",    0x004002, 0x00f00f, Instr.fmt_RRI8_disp ),
        ("s16i",   0x005002, 0x00f00f, Instr.fmt_RRI8_disp16 ),
        ("s32c1i", 0x00e002, 0x00f00f, Instr.fmt_RRI8_s32c1a ),
        ("s32e",   0x490000, 0x00f00f, Instr.fmt_RRI4 ),
        ("s32i",   0x006002, 0x00f00f, Instr.fmt_RRI8_disp32 ),
        ("s32ri",  0x00f002, 0x00f00f, Instr.fmt_RRI8_disp32 ),
        ("sext",   0x230000, 0xff000f, Instr.fmt_RRR_sext ),
        ("sll",    0xa10000, 0xff00ff, Instr.fmt_RRR_sll ),
        ("slli",   0x010000, 0xef000f, Instr.fmt_RRR_slli ),
        ("sra",    0xb10000, 0xff0f0f, Instr.fmt_RRR_2rr ),
        ("srai",   0x210000, 0xef000f, Instr.fmt_RRR_srai ),
        ("src",    0x810000, 0xff000f, Instr.fmt_RRR ),
        ("srl",    0x910000, 0xff0f0f, Instr.fmt_RRR_2rr ),
        ("srli",   0x410000, 0xff000f, Instr.fmt_RRR_sh ),
        ("ssa8b",  0x403000, 0xfff0ff, Instr.fmt_RRR_ssa ),
        ("ssa8l",  0x402000, 0xfff0ff, Instr.fmt_RRR_ssa ),
        ("ssai",   0x404000, 0xfff0ef, Instr.fmt_RRR_ssai ),
        ("ssi",    0x004003, 0x00f00f, Instr.fmt_RRI8 ),
        ("ssiu",   0x00c003, 0x00f00f, Instr.fmt_RRI8 ),
        ("ssl",    0x401000, 0xfff0ff, Instr.fmt_RRR_ssa ),
        ("ssr",    0x400000, 0xfff0ff, Instr.fmt_RRR_ssa ),
        ("ssx",    0x480000, 0xff000f, Instr.fmt_RRR ),
        ("ssx",    0x580000, 0xff000f, Instr.fmt_RRR ),
        ("sub",    0xc00000, 0xff000f, Instr.fmt_RRR ),
        ("sub.s",  0x1a0000, 0xff000f, Instr.fmt_RRR ),
        ("subx2",  0xd00000, 0xff000f, Instr.fmt_RRR ),
        ("subx4",  0xe00000, 0xff000f, Instr.fmt_RRR ),
        ("subx8",  0xf00000, 0xff000f, Instr.fmt_RRR ),
        ("syscall",0x005000, 0xffffff, Instr.fmt_NONE ),
        ("trunc.s",0x9a0000, 0xff000f, Instr.fmt_RRR_ceil ),
        ("ueq.s",  0x3b0000, 0xff000f, Instr.fmt_RRR ),
        ("ufloat.s",      0xda0000, 0xff000f, Instr.fmt_RRR_ceil ),
        ("ule.s",  0x7b0000, 0xff000f, Instr.fmt_RRR ),
        ("ult.s",  0x5b0000, 0xff000f, Instr.fmt_RRR ),
        ("un.s",   0x1b0000, 0xff000f, Instr.fmt_RRR ),
        ("utrunc.s",      0xea0000, 0xff000f, Instr.fmt_RRR_ceil ),
        ("waiti",  0x007000, 0xfff0ff, Instr.fmt_RRR_1imm ),
        ("wdtlb",  0x50e000, 0xfff00f, Instr.fmt_RRR_2r ),
        ("wfr",    0xfa0050, 0xff00ff, Instr.fmt_RRR_sll ),
        ("witlb",  0x506000, 0xfff00f, Instr.fmt_RRR_2r ),
        ("wsr.intenable", 0x13e400, 0xffff0f, Instr.fmt_RSR_spec ),
        ("wsr.litbase",   0x130500, 0xffff0f, Instr.fmt_RSR_spec ),
        ("wsr.vecbase",   0x13e700, 0xffff0f, Instr.fmt_RSR_spec ),
        ("wsr.ps",        0x13e600, 0xffff0f, Instr.fmt_RSR_spec ),
        ("wsr.epc1",      0x13b100, 0xffff0f, Instr.fmt_RSR_spec ),
        ("wsr.ccompare0", 0x13f000, 0xffff0f, Instr.fmt_RSR_spec ),
        ("wsr.intclear",  0x13e300, 0xffff0f, Instr.fmt_RSR_spec ),
        ("wsr.sar",       0x130300, 0xffff0f, Instr.fmt_RSR_spec ),
        ("wsr",    0x130000, 0xff000f, Instr.fmt_RSR ),
        ("xor",    0x300000, 0xff000f, Instr.fmt_RRR ),
        ("xorb",   0x420000, 0xff000f, Instr.fmt_RRR ),
        ("xsr",    0x610000, 0xff000f, Instr.fmt_RSR ),

        ("add.n",   0x000a, 0x000f, Instr.fmt_RRRN ),
        ("addi.n",  0x000b, 0x000f, Instr.fmt_RRRN_addi ),
        ("beqz.n",  0x008c, 0x00cf, Instr.fmt_RI6, CF_JUMP ),
        ("bnez.n",  0x00cc, 0x00cf, Instr.fmt_RI6, CF_JUMP ),
        ("mov.n",   0x000d, 0xf00f, Instr.fmt_RRRN_2r ),
        ("break.n", 0xf02d, 0xf0ff, Instr.fmt_RRRN ),
        ("ret.n",   0xf00d, 0xffff, Instr.fmt_NNONE, CF_STOP ),
        ("retw.n",  0xf01d, 0xffff, Instr.fmt_NNONE, CF_STOP ),
        ("l32i.n",  0x0008, 0x000f, Instr.fmt_RRRN_disp ),
        ("movi.n",  0x000c, 0x008f, Instr.fmt_RI7 ),
        ("nop.n",   0xf03d, 0xffff, Instr.fmt_NNONE ),
        ("s32i.n",  0x0009, 0x000f, Instr.fmt_RRRN_disp ),
        ("ill.n",  0xf06d, 0xffff, Instr.fmt_NONE ),
    )

    def __init__(self):
        processor_t.__init__(self)
        self._init_instructions()
        self._init_registers()

    def _add_instruction(self, instr):
        self.instrs_list.append(instr)

    def _init_instructions(self):
        self.instrs_list = []
        self.short_insts = []
        self.long_insts = []

        for o in self.ops:
            instr = Instr(*o)
            self._add_instruction(instr)
            if instr.size == 2:
                self.short_insts.append(instr)
            else:
                self.long_insts.append(instr)

        self.instruc = [{ "name": i.name, "feature": i.flags } for i in self.instrs_list]
        self.instruc_end = len(self.instruc)

        self.instrs = {}
        for instr in self.instrs_list:
            self.instrs[instr.name] = instr

        self.instrs_ids = {}
        for i, instr in enumerate(self.instrs_list):
            self.instrs_ids[instr.name] = i
            instr.id = i

    def _init_registers(self):
        self.reg_names = ["a%d" % d for d in range(16)]
        self.reg_names += ["pc", "sar", "CS", "DS"]
        self.reg_ids = {}
        for i, reg in enumerate(self.reg_names):
            self.reg_ids[reg] = i

        self.reg_first_sreg = self.reg_code_sreg = self.reg_ids["CS"]
        self.reg_last_sreg = self.reg_data_sreg = self.reg_ids["DS"]

    def _pull_op_byte(self, insn):
        ea = insn.ea + insn.size
        byte = get_wide_byte(ea)
        insn.size += 1
        return byte

    def _find_instr(self, insn):
        op = self._pull_op_byte(insn)
        op |= self._pull_op_byte(insn) << 8

        for instr in self.short_insts:
            if instr.match(op):
                return instr, op

        op |= self._pull_op_byte(insn) << 16

        for instr in self.long_insts:
            if instr.match(op):
                return instr, op

        return None, op

    def notify_ana(self, insn):
        instr, op = self._find_instr(insn)
        if not instr:
            # sometimes a 0x00 is used as padding at the end of a function
            # so it has to be ignored to detect function properly
            # this may be en issue sometimes but for what I've seend there not opcode using 0 as first byte
            if op == 0:
                insn.itype = self.instrs_ids["ill"]
                return 1
            return 0

        insn.itype = instr.id

        operands = [insn[i] for i in xrange(1, 6)]
        for o in operands:
            o.type = o_void
        instr.parseOperands(operands, op, insn)

        return insn.size

    def emu(self, insn):
        for i in xrange(1, 6):
            op = insn[i]
            if op.type == o_void:
                break
            elif op.type == o_mem:
                insn.create_op_data(op.addr, 0, op.dtyp)
                insn.add_dref(op.addr, 0, dr_R)
            elif op.type == o_near:
                features = insn.get_canon_feature()
                if features & CF_CALL:
                    fl = fl_CN
                else:
                    fl = fl_JN
                insn.add_cref(op.addr, 0, fl)

        feature = insn.get_canon_feature()
        if feature & CF_JUMP:
            remember_problem(Q_jumps, insn.ea)
        if not feature & CF_STOP:
            insn.add_cref(insn.ea + insn.size, 0, fl_F)
        return True

    notify_emu = emu

    def outop(self, ctx, op):
        if op.type == o_reg:
            ctx.out_register(self.reg_names[op.reg])
        elif op.type == o_imm:
            instr = self.instrs_list[ctx.insn.itype]
            if instr.name in ("extui", "bbci", "bbsi", "slli", "srli", "srai", "ssai"):
                # bit numbers/shifts are always decimal
                ctx.out_long(op.value, 10)
            else:
                ctx.out_value(op, OOFW_IMM)
        elif op.type in (o_near, o_mem):
            ok = ctx.out_name_expr(op, op.addr, BADADDR)
            if not ok:
                ctx.out_tagon(COLOR_ERROR)
                ctx.out_long(op.addr, 16)
                ctx.out_tagoff(COLOR_ERROR)
                remember_problem(Q_noName, ctx.insn.ea)
        elif op.type == o_displ:
            ctx.out_register(self.reg_names[op.phrase])
            ctx.out_line(", ")
            ctx.out_value(op, OOF_ADDR)
        else:
            return False
        return True

    notify_out_operand = outop

    def out_mnem(self, ctx):
        ctx.out_mnem(15, "")

    def notify_out_insn(self, ctx):
        ctx.out_mnemonic()
        for i in xrange(1, 6):
            if ctx.insn[i].type == o_void:
                break

            if i > 0:
                ctx.out_symbol(',')
            ctx.out_char(' ')
            ctx.out_one_operand(i)

        ctx.set_gen_cmt()
        ctx.flush_outbuf()


def PROCESSOR_ENTRY():
    return XtensaProcessor()

if __name__ == "__main__":
    class DummyProcessor(XtensaProcessor):
        def __init__(self, b):
            XtensaProcessor.__init__(self)
            self.b = b

        def _pull_op_byte(self):
            return self.b.pop(0)

    def disasm(b):
        dp = DummyProcessor([ord(ch) for ch in b])
        instr, op = dp._find_instr()
        assert instr

        class cmd(object):
            ea = 1234

        instr.operands = []
        for operand in instr.fmt:
            o = copy.copy(operand)
            operand.parse(o, op, cmd)
            instr.operands.append(o)
        return instr

    assert disasm("\x36\x61\x00").name == "entry"
    assert disasm("\xd0\x04\x00").name == "callx4"
    assert disasm("\xe0\x08\x00").name == "callx8"
    assert disasm("\xf0\x00\x00").name == "callx12"
    assert disasm("\x1d\xf0").name == "retw.n"
    assert disasm("\x55\xa2\x28").name == "call4"
    assert disasm("\xe5\xc7\x01").name == "call8"
    assert disasm("\x75\x0c\xa9").name == "call12"
    assert disasm("\x00\xbb\x23").name == "sext"
    assert disasm("\x20\xba\xa2").name == "muluh"
    assert disasm("\x2c\x08").name == "movi.n"
    assert disasm("\x2c\x08").operands[0].reg == 8
    assert disasm("\x2c\x08").operands[1].value == 32
    assert disasm("\x1c\x68").operands[1].value == 22
    assert disasm("\x4c\x00").operands[1].value == 64
    assert disasm("\x6c\x11").operands[1].value == -31