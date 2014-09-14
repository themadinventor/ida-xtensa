from idaapi import *

GREETINGS_STRING = """\
Tensilica Xtensa processor for IDA (C) 2014 Fredrik Ahlberg\
"""

class OpType:
	NONE		= 0
	NNONE		= 1
	RRR		= 2
	RRR_1imm	= 3
	RRR_2imm	= 4
	RRI8		= 5
	RI16		= 6
	BRI8		= 7
	BRI12		= 8
	CALL		= 9
	CALLX		= 10
	RSR		= 11
	RSR_spec	= 12
	RRRN		= 13
	RI6		= 14
	RI7		= 15

	REG	= 0
	IMM	= 1
	MEM	= 2
	RELA	= 3

class Operand:
	def __init__(self, type, size, rshift, size2 = 0, rshift2 = 0):
		self.type = type
		self.size = size
		self.rshift = rshift
		self.size2 = size2
		self.rshift2 = rshift2

	def parse(self, ret, op, cmd = None):
		val = (op >> self.rshift) & (0xffffffff >> (32-self.size))
		if self.size2:
			val |= (op >> self.rshift2) & (0xffffffff >> (32-self.size2)) << self.size

		#print '<Op %d, %x>' % (self.type, val)

		if self.type == OpType.REG:
			ret.type = o_reg
			ret.dtyp = dt_byte
			ret.reg = val if val < 16 else 16
		elif self.type == OpType.IMM:
			ret.type = o_imm
			ret.dtyp = dt_byte
			ret.value = val
		elif self.type == OpType.MEM:
			ret.type = o_mem
			ret.dtyp = dt_byte
			ret.addr = val
		elif self.type == OpType.RELA:
			ret.type = o_near
			ret.dtyp = dt_byte
			ret.addr = val + cmd.ea + 4
		else:
			raise ValueError("unhandled operand type");

class Instr(object):

	fmts = (
		# 0. NONE
		(),
		# 1. NNONE
		(),
		# 2. RRR
		(Operand(OpType.REG, 4, 12), Operand(OpType.REG, 4, 8), Operand(OpType.REG, 4, 4)),
		# 3. RRR_1imm
		(Operand(OpType.IMM, 4, 8),),
		# 4. RRR_2imm
		(Operand(OpType.IMM, 4, 8), Operand(OpType.IMM, 4, 4)),
		# 5. RRI8
		(Operand(OpType.IMM, 8, 16), Operand(OpType.REG, 4, 12), Operand(OpType.REG, 4, 8), Operand(OpType.REG, 4, 4)),
		# 6. RI16
		(Operand(OpType.REG, 4, 4), Operand(OpType.IMM, 16, 8)),
		# 7. BRI8
		(Operand(OpType.REG, 4, 12), Operand(OpType.REG, 4, 8), Operand(OpType.RELA, 8, 16)),
		# 8. BRI12
		(Operand(OpType.REG, 4, 8), Operand(OpType.RELA, 12, 12)),
		# 9. CALL
		(Operand(OpType.RELA, 18, 6),),
		# 10. CALLX
		(Operand(OpType.REG, 4, 8),),
		# 11. RSR
		(Operand(OpType.IMM, 8, 8), Operand(OpType.REG, 4, 4)),
		# 12. RSR_spec
		(Operand(OpType.REG, 4, 4),),
		# 13. RRRN
		(Operand(OpType.REG, 4, 12), Operand(OpType.REG, 4, 8), Operand(OpType.REG, 4, 4)),
		# 14. RI6
		(Operand(OpType.REG, 4, 8), Operand(OpType.RELA, 4, 12, 2, 4)),
		# 15. RI7
		(Operand(OpType.REG, 4, 8), Operand(OpType.IMM, 4, 12, 3, 4))
		)

	def __init__(self, name, opcode, mask, fmt, flags = 0):
		self.name = name
		self.opcode = opcode
		self.mask = mask

		self.fmt = Instr.fmts[fmt]

		self.flags = flags
		self.size = 2 if fmt in (OpType.RRRN, OpType.RI6, OpType.RI7, OpType.NNONE) else 3
	
	def match(self, op):
		return (op & self.mask) == self.opcode

	def parseOperands(self, operands, op, cmd = None):
		for ret, fmt in zip(operands, self.fmt):
			fmt.parse(ret, op, cmd)
	
	def __str__(self):
		return "<Instr %s %x/%x>" % (self.name, self.opcode, self.mask)

class XtensaProcessor(processor_t):
	id = 0x8000 + 1990
	flag = PR_ADJSEGS | PRN_HEX | PR_WORD_INS
	cnbits = 8
	dnbits = 8
	psnames = ["xtensa"]
	plnames = ["Tensilica Xtensa"]
	segreg_size = 0

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
		"a_byte": ".word",
		"a_word": ".dword",
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
		("abs",    0x600100, 0xff0f0f, OpType.RRR ),
		("add",	   0x800000, 0xff000f, OpType.RRR ),
		("addi",   0x00c002, 0x00f00f, OpType.RRI8 ),
		("addmi",  0x00d002, 0x00f00f, OpType.RRI8 ),
		("addx2",  0x900000, 0xff000f, OpType.RRR ),
		("addx4",  0xa00000, 0xff000f, OpType.RRR ),
		("addx8",  0xb00000, 0xff000f, OpType.RRR ),
		("and",    0x100000, 0xff000f, OpType.RRR ),
		("ball",   0x004007, 0x00f00f, OpType.RRI8 ),
		("bany",   0x008007, 0x00f00f, OpType.RRI8 ),
		("bbc",    0x005007, 0x00f00f, OpType.RRI8 ),
		("bbs",    0x00d007, 0x00f00f, OpType.RRI8 ),
		("bbci",   0x006007, 0x00e00f, OpType.RRI8 ),
		("bbsi",   0x00e007, 0x00e00f, OpType.RRI8 ),
		("beq",    0x001007, 0x00f00f, OpType.RRI8 ),
		("beqi",   0x000026, 0x0000ff, OpType.RRI8 ),
		("beqz",   0x000016, 0x0000ff, OpType.BRI12 ),
		("bge",    0x00a007, 0x00f00f, OpType.RRI8 ),
		("bgei",   0x0000e6, 0x0000ff, OpType.BRI8 ),
		("bgeu",   0x00b007, 0x00f00f, OpType.RRI8 ),
		("bgeui",  0x0000f6, 0x0000ff, OpType.BRI8 ),
		("bgez",   0x0000d6, 0x0000ff, OpType.BRI12 ),
		("blt",    0x002007, 0x00f00f, OpType.RRI8 ),
		("blti",   0x0000a6, 0x0000ff, OpType.BRI8 ),
		("bltu",   0x003007, 0x00f00f, OpType.RRI8 ),
		("bltui",  0x0000b6, 0x0000ff, OpType.BRI8 ),
		("bltz",   0x000096, 0x0000ff, OpType.BRI12 ),
		("bnall",  0x00c007, 0x00f00f, OpType.RRI8 ),
		("bnone",  0x000007, 0x00f00f, OpType.RRI8 ),
		("bne",    0x009007, 0x00f00f, OpType.RRI8 ),
		("bnei",   0x000066, 0x0000ff, OpType.BRI8 ),
		("bnez",   0x000056, 0x0000ff, OpType.BRI12 ),
		("break",  0x004000, 0xfff00f, OpType.RRR_2imm ),
		("call0",  0x000005, 0x00003f, OpType.CALL, CF_CALL ),
		("callx0", 0x0000c0, 0xfff0ff, OpType.CALLX, CF_CALL ),
		("dsync",  0x002030, 0xffffff, OpType.NONE ),
		("esync",  0x002020, 0xffffff, OpType.NONE ),
		("extui",  0x040000, 0x0e000f, OpType.RRR ),
		("extw",   0x0020d0, 0xffffff, OpType.RRR ),
		("isync",  0x002000, 0xffffff, OpType.NONE ),
		("j",      0x000006, 0x00003f, OpType.CALL, CF_JUMP ),
		("jx",     0x0000a0, 0xfff0ff, OpType.CALLX, CF_JUMP ),
		("l8ui",   0x000002, 0x00f00f, OpType.RRI8 ),
		("l16si",  0x009002, 0x00f00f, OpType.RRI8 ),
		("l16ui",  0x001002, 0x00f00f, OpType.RRI8 ),
		("l32i",   0x002002, 0x00f00f, OpType.RRI8 ),
		("l32r",   0x000001, 0x00000f, OpType.RI16 ),
		("memw",   0x0020c0, 0xffffff, OpType.NONE ),
		("moveqz", 0x830000, 0xff000f, OpType.RRR ),
		("movgez", 0xb30000, 0xff000f, OpType.RRR ),
		("movi",   0x00a002, 0x00f00f, OpType.RRI8 ),
		("movltz", 0xa30000, 0xff000f, OpType.RRR ),
		("movnez", 0x930000, 0xff000f, OpType.RRR ),
		("neg",    0x300000, 0xff0f0f, OpType.RRR ),
		("nop",    0x0020f0, 0xffffff, OpType.NONE ),
		("or",     0x200000, 0xff000f, OpType.RRR ),
		("ret",    0x000080, 0xffffff, OpType.NONE, CF_STOP ),
		("rfe",    0x003000, 0xffffff, OpType.NONE, CF_STOP ),
		("rfi",    0x003010, 0xfff0ff, OpType.RRR_1imm, CF_STOP ),
		("rsil",   0x006000, 0xfff00f, OpType.RRR ),
		("rsr",    0x030000, 0xff000f, OpType.RSR ),
		("rsync",  0x002010, 0xffffff, OpType.NONE ),
		("s8i",    0x004002, 0x00f00f, OpType.RRI8 ),
		("s16i",   0x005002, 0x00f00f, OpType.RRI8 ),
		("s32i",   0x006002, 0x00f00f, OpType.RRI8 ),
		("sll",    0xa10000, 0xff00ff, OpType.RRR ),
		("slli",   0x010000, 0xef000f, OpType.RRR ),
		("sra",    0xb10000, 0xff0f0f, OpType.RRR ),
		("srai",   0x210000, 0xef000f, OpType.RRR ),
		("src",    0x810000, 0xff000f, OpType.RRR ),
		("srl",    0x910000, 0xff0f0f, OpType.RRR ),
		("srli",   0x410000, 0xff000f, OpType.RRR ),
		("ssa8b",  0x403000, 0xfff0ff, OpType.RRR ),
		("ssa8l",  0x402000, 0xfff0ff, OpType.RRR ),
		("ssai",   0x404000, 0xfff0ef, OpType.RRR ),
		("ssl",    0x401000, 0xfff0ff, OpType.RRR ),
		("ssr",    0x400000, 0xfff0ff, OpType.RRR ),
		("sub",    0xc00000, 0xff000f, OpType.RRR ),
		("subx2",  0xd00000, 0xff000f, OpType.RRR ),
		("subx4",  0xe00000, 0xff000f, OpType.RRR ),
		("subx8",  0xf00000, 0xff000f, OpType.RRR ),
		("waiti",  0x007000, 0xfff0ff, OpType.RRR_1imm ),
		("wdtlb",  0x50e000, 0xfff00f, OpType.RRR ),
		("witlb",  0x506000, 0xfff00f, OpType.RRR ),
		("wsr.intenable", 0x13e400, 0xffff0f, OpType.RSR_spec ),
		("wsr.litbase",   0x130500, 0xffff0f, OpType.RSR_spec ),
		("wsr.vecbase",   0x13e700, 0xffff0f, OpType.RSR_spec ),
		("wsr.ps",        0x13e400, 0xffff0f, OpType.RSR_spec ),
		("wsr.epc1",      0x13b100, 0xffff0f, OpType.RSR_spec ),
		("wsr.ccompare0", 0x13f000, 0xffff0f, OpType.RSR_spec ),
		("wsr.intclear",  0x13e300, 0xffff0f, OpType.RSR_spec ),
		("wsr.sar",       0x130300, 0xffff0f, OpType.RSR_spec ),
		("wsr",    0x130000, 0xff000f, OpType.RSR ),
		("xor",    0x300000, 0xff000f, OpType.RRR ),
		("xsr",    0x610000, 0xff000f, OpType.RSR ),

		("add.n",   0x000a, 0x000f, OpType.RRRN ),
		("addi.n",  0x000b, 0x000f, OpType.RRRN ),
		("beqz.n",  0x008c, 0x00cf, OpType.RI6 ),
		("bnez.n",  0x00cc, 0x00cf, OpType.RI6 ),
		("mov.n",   0x000d, 0xf00f, OpType.RRRN ),
		("break.n", 0xf02d, 0xf0ff, OpType.RRRN ),
		("ret.n",   0xf00d, 0xffff, OpType.NNONE, CF_STOP ),
		("l32i.n",  0x0008, 0x000f, OpType.RRRN ),
		("movi.n",  0x000c, 0x008f, OpType.RI7 ),
		("nop.n",   0xf03d, 0xffff, OpType.NNONE ),
		("s32i.n",  0x0009, 0x000f, OpType.RRRN ),
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
		self.regNames = ["a%d" % d for d in xrange(16)]
		self.regNames += ["pc", "sar", "$CS", "$DS"]
		self.reg_ids = {}
		for i, reg in enumerate(self.regNames):
			self.reg_ids[reg] = i

		self.regFirstSreg = self.regCodeSreg = self.reg_ids["$CS"]
		self.regLastSreg = self.regDataSreg = self.reg_ids["$DS"]
	
	def _pull_op_byte(self):
		ea = self.cmd.ea + self.cmd.size
		byte = get_full_byte(ea)
		self.cmd.size += 1
		return byte

	def _find_instr(self):
		op = self._pull_op_byte()
		op |= self._pull_op_byte() << 8
		#print 'ana: %04x' % op
		
		for instr in self.short_insts:
			if instr.match(op):
				#print 'ana: short hit', instr
				return instr, op

		op |= self._pull_op_byte() << 16
		#print 'ana: %06x' % op

		for instr in self.long_insts:
			if instr.match(op):
				#print 'ana: long hit', instr
				return instr, op

		print 'xtensa: no such instruction %06x' % op
		return None, op

	def ana(self):
		instr, op = self._find_instr()
		if not instr:
			return 0
		
		self.cmd.itype = instr.id

		operands = [self.cmd[i] for i in xrange(6)]
		for o in operands:
			o.type = o_void
		instr.parseOperands(operands, op, self.cmd)

		return self.cmd.size

	def emu(self):
		if not self.cmd.get_canon_feature() & CF_STOP:
			ua_add_cref(0, self.cmd.ea + self.cmd.size, fl_F)
		return True
	
	def outop(self, op):
		if op.type == o_reg:
			out_register(self.regNames[op.reg])
		elif op.type == o_imm:
			OutValue(op, OOFW_IMM)
		elif op.type in (o_near, o_mem):
			ok = out_name_expr(op, op.addr, BADADDR)
			if not ok:
				out_tagon(COLOR_ERROR)
				OutLong(op.addr, 16)
				out_tagoff(COLOR_ERROR)
				QueueMark(Q_noName, self.cmd.ea)
		else:
			return False
		return True

	def out(self):
		buf = init_output_buffer(1024)
		OutMnem(15)

		instr = self.instrs_list[self.cmd.itype]

		for i in xrange(6):
			if self.cmd[i].type == o_void:
				break

			if i > 0:
				out_symbol(',')
			OutChar(' ')
			out_one_operand(i)

		term_output_buffer()
		cvar.gl_comm = 1
		MakeLine(buf)


def PROCESSOR_ENTRY():
	return XtensaProcessor()
