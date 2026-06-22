#!/usr/bin/env python3
"""MIPS32 LE Unicorn oracle — generates a golden vector corpus for MipsVecCheck.

Groups covered (no branches/CP0 — those have dedicated Lean-only tests):
  alu-r    : ADDU SUBU AND OR XOR NOR SLL SRL SRA SLLV SRLV SRAV SLT SLTU
  alu-i    : ADDIU ANDI ORI XORI SLTI SLTIU LUI
  muldiv   : MULT MULTU DIV DIVU MFHI MFLO MTHI MTLO
  special2 : MUL CLZ CLO
  special3 : EXT INS

Usage:
  python3 tools/mipsgen/mips_oracle.py tests/mipsvec/mips32-vectors.json
"""

import json, struct, random, sys
from unicorn import *
from unicorn.mips_const import *

random.seed(0x13373456)

CODE      = 0x10000        # physical code address in Unicorn's flat space
CODE_VIRT = 0x80000000    # kseg0 virtual code address in SEI (must match MipsVecCheck.lean)
HI_REG = UC_MIPS_REG_HI
LO_REG = UC_MIPS_REG_LO
REG0   = UC_MIPS_REG_0   # base; UC_MIPS_REG_0 + i = GPR i

def r_type(rs, rt, rd, sa, funct, op=0):
    return ((op&0x3f)<<26)|((rs&0x1f)<<21)|((rt&0x1f)<<16)|((rd&0x1f)<<11)|((sa&0x1f)<<6)|(funct&0x3f)

def i_type(op, rs, rt, imm):
    return ((op&0x3f)<<26)|((rs&0x1f)<<21)|((rt&0x1f)<<16)|(imm&0xFFFF)

def run_insn(word, in_regs, in_hi=0, in_lo=0):
    """Execute one instruction, return (out_regs[32], out_hi, out_lo) or None on error."""
    mu = Uc(UC_ARCH_MIPS, UC_MODE_MIPS32 + UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE & ~0xFFF, 0x3000)
    mu.mem_write(CODE, struct.pack('<II', word, 0))   # insn + NOP delay slot
    for i, v in enumerate(in_regs):
        if i == 0:
            continue   # $zero is always 0
        mu.reg_write(REG0 + i, v & 0xFFFFFFFF)
    mu.reg_write(HI_REG, in_hi & 0xFFFFFFFF)
    mu.reg_write(LO_REG, in_lo & 0xFFFFFFFF)
    try:
        mu.emu_start(CODE, CODE + 0x2000, count=1)
    except UcError:
        return None
    out_regs = [mu.reg_read(REG0 + i) for i in range(32)]
    return (out_regs, mu.reg_read(HI_REG), mu.reg_read(LO_REG))

# ---------------------------------------------------------------------------
# Input data sets
# ---------------------------------------------------------------------------

# 32 base register values used across tests; index 0 is always 0 ($zero).
BASE_REGS = [
    0,              # r0  = $zero, always 0
    1,              # r1
    0xFFFFFFFF,     # r2  = -1
    0x80000000,     # r3  = INT_MIN
    0x7FFFFFFF,     # r4  = INT_MAX
    100,            # r5
    0xDEADBEEF,     # r6
    0x12345678,     # r7
    0xABCDEF01,     # r8
    42,             # r9
    0,              # r10 (second zero for SUBU/SLTU edge cases)
    0xFFFF,         # r11
    0x80000001,     # r12
    0x7FFFFFFE,     # r13
    0x55555555,     # r14
    0xAAAAAAAA,     # r15
    0x0000FFFF,     # r16
    0xFFFF0000,     # r17
    0x01010101,     # r18
    0xFEFEFEFE,     # r19
    17,             # r20
    31,             # r21 (max shift amount)
    0,              # r22
    1,              # r23
    2,              # r24
    3,              # r25
    0,              # r26 (k0)
    0,              # r27 (k1)
    0,              # r28 (gp)
    0xBFC00000,     # r29 (sp)
    0,              # r30 (fp)
    0,              # r31 (ra)
]

def make_regs(**kwargs):
    """Return a copy of BASE_REGS with selected registers overridden."""
    r = list(BASE_REGS)
    for k, v in kwargs.items():
        r[int(k[1:])] = v & 0xFFFFFFFF
    return r

# Random reg sets for broader coverage
RAND_REGS_SETS = [
    [0] + [random.randint(0, 0xFFFFFFFF) for _ in range(31)]
    for _ in range(6)
]

SMALL_VALUES = [0, 1, 2, 3, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFE, 0xFFFFFFFF]
SHIFT_AMOUNTS = [0, 1, 7, 8, 15, 16, 23, 24, 31]

# ---------------------------------------------------------------------------
# Vector generators
# ---------------------------------------------------------------------------

vectors = []

def emit(group, word, in_regs, in_hi=0, in_lo=0):
    res = run_insn(word, in_regs, in_hi, in_lo)
    if res is None:
        return
    out_regs, out_hi, out_lo = res
    vectors.append({
        "group": group,
        "insn": word,
        "in_regs": list(in_regs),
        "in_hi": in_hi,
        "in_lo": in_lo,
        "out_regs": out_regs,
        "out_hi": out_hi,
        "out_lo": out_lo,
    })

def emit_link(group, word, in_regs, in_hi=0, in_lo=0):
    """Like emit() but translate r31 link value from oracle's CODE+8 to SEI's CODE_VIRT+8.
    Link-branch instructions (JAL/BLTZAL/BGEZAL/BLTZALL/BGEZALL) set r31 = PC+8.
    Oracle PC = CODE; SEI PC = CODE_VIRT. Must adjust so checker passes."""
    res = run_insn(word, in_regs, in_hi, in_lo)
    if res is None:
        return
    out_regs, out_hi, out_lo = res
    out_regs = list(out_regs)
    if out_regs[31] == CODE + 8:
        out_regs[31] = CODE_VIRT + 8
    vectors.append({
        "group": group,
        "insn": word,
        "in_regs": list(in_regs),
        "in_hi": in_hi,
        "in_lo": in_lo,
        "out_regs": out_regs,
        "out_hi": out_hi,
        "out_lo": out_lo,
    })

# ── ALU-R ──────────────────────────────────────────────────────────────────

def gen_alu_r():
    # Register triples: (rs, rt, rd) — avoid r0 as destination to keep $zero clean
    triples = [(1, 2, 3), (4, 5, 6), (7, 8, 9), (10, 11, 12), (2, 3, 4)]
    # Dyadic ops: funct → name
    dyadic = [
        (0x21, "addu"), (0x23, "subu"), (0x24, "and"), (0x25, "or"),
        (0x26, "xor"), (0x27, "nor"), (0x2A, "slt"), (0x2B, "sltu"),
    ]
    regs_sets = [BASE_REGS] + RAND_REGS_SETS[:3]
    for funct, _ in dyadic:
        for (rs, rt, rd) in triples[:3]:
            for regs in regs_sets:
                emit("alu-r", r_type(rs, rt, rd, 0, funct), regs)

    # Immediate shifts: SLL/SRL/SRA (rs=0 field ignored, rt=src, rd=dst, sa=amount)
    for funct, _ in [(0x00, "sll"), (0x02, "srl"), (0x03, "sra")]:
        for rt, rd in [(1, 3), (4, 6), (7, 9)]:
            for sa in SHIFT_AMOUNTS:
                for regs in regs_sets[:2]:
                    emit("alu-r", r_type(0, rt, rd, sa, funct), regs)
            # Edge: shift rt=r2(0xFFFFFFFF), r3(0x80000000), r4(0x7FFFFFFF)
            for val_reg in [2, 3, 4]:
                for sa in [0, 1, 15, 31]:
                    emit("alu-r", r_type(0, val_reg, 9, sa, funct), BASE_REGS)

    # Register shifts: SLLV/SRLV/SRAV (rs=shift_reg, rt=src, rd=dst)
    for funct, _ in [(0x04, "sllv"), (0x06, "srlv"), (0x07, "srav")]:
        # r21 = 31 in BASE_REGS, r1 = 1, r9 = 42
        for rs, rt, rd in [(20, 1, 3), (21, 4, 6), (1, 7, 9), (9, 3, 5)]:
            for regs in regs_sets[:2]:
                emit("alu-r", r_type(rs, rt, rd, 0, funct), regs)
        # Shift by 0, 1, 31, 32 (32 wraps to 0 in MIPS: only low 5 bits used)
        for sa_reg in [10, 1, 21, 24]:  # r10=0, r1=1, r21=31, r24=2
            emit("alu-r", r_type(sa_reg, 2, 9, 0, 0x04), BASE_REGS)
            emit("alu-r", r_type(sa_reg, 3, 9, 0, 0x06), BASE_REGS)
            emit("alu-r", r_type(sa_reg, 3, 9, 0, 0x07), BASE_REGS)

gen_alu_r()

# ── ALU-I ──────────────────────────────────────────────────────────────────

def gen_alu_i():
    # (op, zero-extend imm?)
    imm_ops = [
        (0x09, "addiu", True),
        (0x0C, "andi",  True),   # zero-extend
        (0x0D, "ori",   True),   # zero-extend
        (0x0E, "xori",  True),   # zero-extend
        (0x0A, "slti",  False),  # sign-extend
        (0x0B, "sltiu", False),  # sign-extend (then compare unsigned)
    ]
    imm_vals = [0, 1, 0x7FFF, 0x8000, 0xFFFF, 100, 0x1234]
    src_pairs = [(1, 2), (3, 4), (5, 6), (7, 8)]
    regs_sets = [BASE_REGS] + RAND_REGS_SETS[:2]
    for op, _, _ in imm_ops:
        for rs, rt in src_pairs[:2]:
            for imm in imm_vals:
                for regs in regs_sets[:2]:
                    emit("alu-i", i_type(op, rs, rt, imm), regs)
    # LUI
    for rt in [1, 3, 5]:
        for imm in [0, 1, 0x7FFF, 0x8000, 0xFFFF, 0x1234]:
            emit("alu-i", i_type(0x0F, 0, rt, imm), BASE_REGS)

gen_alu_i()

# ── MULDIV ─────────────────────────────────────────────────────────────────

def gen_muldiv():
    # MULT / MULTU — inputs: (rs, rt) register indices, registers must have good values
    mult_pairs = [
        (1, 5),     # 1 * 100
        (4, 1),     # INT_MAX * 1
        (3, 1),     # INT_MIN * 1
        (2, 24),    # -1 * 2
        (4, 24),    # INT_MAX * 2 (overflows signed product)
        (3, 24),    # INT_MIN * 2
        (2, 2),     # -1 * -1 = +1
        (3, 3),     # INT_MIN * INT_MIN (large)
        (5, 9),     # 100 * 42
        (6, 7),     # DEADBEEF * 12345678
    ]
    for funct, name in [(0x18, "mult"), (0x19, "multu")]:
        for rs, rt in mult_pairs:
            emit("muldiv", r_type(rs, rt, 0, 0, funct), BASE_REGS)
        for rset in RAND_REGS_SETS[:3]:
            emit("muldiv", r_type(1, 2, 0, 0, funct), rset)

    # DIV / DIVU — avoid zero divisor
    div_pairs = [
        (5, 24),    # 100 / 2  = 50 r0
        (5, 9),     # 100 / 42 = 2 r16
        (2, 1),     # -1 / 1   = -1 r0
        (2, 24),    # -1 / 2   = 0 r-1 (truncate: 0 remainder -1)
        (3, 24),    # INT_MIN / 2 = -2^30 r0
        (4, 5),     # INT_MAX / 100
        (5, 2),     # 100 / -1 = -100 r0
        (1, 5),     # 1 / 100 = 0 r1
        (9, 5),     # 42 / 100 = 0 r42
    ]
    for funct, name in [(0x1A, "div"), (0x1B, "divu")]:
        for rs, rt in div_pairs:
            emit("muldiv", r_type(rs, rt, 0, 0, funct), BASE_REGS)

    # MFHI / MFLO — set known HI/LO, verify they land in rd
    for hi_val, lo_val in [(0x12345678, 0xDEADBEEF), (0, 0), (0xFFFFFFFF, 0x80000000),
                            (1, 0x7FFFFFFF), (0xABCDEF01, 0x00000001)]:
        emit("muldiv", r_type(0, 0, 3, 0, 0x10), BASE_REGS, in_hi=hi_val, in_lo=lo_val)  # MFHI
        emit("muldiv", r_type(0, 0, 3, 0, 0x12), BASE_REGS, in_hi=hi_val, in_lo=lo_val)  # MFLO

    # MTHI / MTLO — write rs to HI/LO
    for src_reg in [1, 2, 3, 4, 5, 7]:
        emit("muldiv", r_type(src_reg, 0, 0, 0, 0x11), BASE_REGS)  # MTHI
        emit("muldiv", r_type(src_reg, 0, 0, 0, 0x13), BASE_REGS)  # MTLO

gen_muldiv()

# ── SPECIAL2 ───────────────────────────────────────────────────────────────

def gen_special2():
    # MUL (op=0x1C, funct=0x02): rd = low32(rs * rt)
    mul_pairs = [(1, 5), (4, 24), (3, 24), (2, 2), (5, 9), (6, 7)]
    for rs, rt in mul_pairs:
        emit("special2", r_type(rs, rt, 3, 0, 0x02, op=0x1C), BASE_REGS)
    for rset in RAND_REGS_SETS[:2]:
        emit("special2", r_type(1, 2, 3, 0, 0x02, op=0x1C), rset)

    # CLZ (op=0x1C, funct=0x20): rd = leading zeros of rs
    # For CLZ: rs=rt per encoding convention; rd is destination
    clz_vals = [0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    for src_reg in [1, 2, 3, 4, 5, 6, 7, 8]:
        emit("special2", r_type(src_reg, src_reg, 3, 0, 0x20, op=0x1C), BASE_REGS)
    # Test specific CLZ values via custom regs
    for val in [0, 1, 2, 0x80000000, 0x40000000, 0x00010000, 0x00000001, 0xFFFFFFFF]:
        regs = make_regs(r1=val)
        emit("special2", r_type(1, 1, 3, 0, 0x20, op=0x1C), regs)

    # CLO (op=0x1C, funct=0x21): rd = leading ones of rs
    for src_reg in [1, 2, 3, 4, 5, 6, 7, 8]:
        emit("special2", r_type(src_reg, src_reg, 3, 0, 0x21, op=0x1C), BASE_REGS)
    for val in [0, 1, 0x80000000, 0xC0000000, 0xFFFF0000, 0xFFFFFFFF, 0xFFFFFFFE, 0x7FFFFFFF]:
        regs = make_regs(r1=val)
        emit("special2", r_type(1, 1, 3, 0, 0x21, op=0x1C), regs)

gen_special2()

# ── SPECIAL3 ───────────────────────────────────────────────────────────────

def gen_special3():
    # EXT (op=0x1F, funct=0x00): rt = (rs >> lsb) & ((1<<size)-1)
    # Encoding: rs=rs, rt=rt, rd=msbd=size-1, sa=lsb=pos
    def ext(rs, rt, pos, size):
        return r_type(rs, rt, size-1, pos, 0x00, op=0x1F)

    ext_cases = [
        (1, 3, 0, 1),   # extract bit 0
        (1, 3, 0, 8),   # extract byte 0
        (1, 3, 8, 8),   # extract byte 1
        (1, 3, 0, 16),  # extract low halfword
        (1, 3, 16, 16), # extract high halfword
        (1, 3, 0, 32),  # extract all 32 bits (pos=0, size=32)
        (1, 3, 31, 1),  # extract bit 31 (sign bit)
        (1, 3, 4, 4),   # extract nibble at pos 4
        (1, 3, 1, 30),  # 30-bit field at pos 1
        (2, 3, 0, 8),   # extract from r2=0xFFFFFFFF
        (4, 3, 0, 8),   # extract from r4=0x7FFFFFFF
        (3, 3, 24, 8),  # extract high byte from r3=0x80000000
        (7, 3, 4, 8),   # extract from r7=0x12345678 → 0x67
        (6, 3, 0, 16),  # extract low16 from r6=0xDEADBEEF → 0xBEEF
    ]
    for rs, rt, pos, size in ext_cases:
        emit("special3", ext(rs, rt, pos, size), BASE_REGS)
    # Random inputs
    for val in [0, 0x12345678, 0xDEADBEEF, 0x80000000, 0x7FFFFFFF, 0xFFFFFFFF]:
        regs = make_regs(r1=val)
        for pos, size in [(0, 8), (8, 8), (0, 32), (4, 4), (28, 4)]:
            emit("special3", ext(1, 3, pos, size), regs)

    # INS (op=0x1F, funct=0x04): rt[msb:lsb] = rs[size-1:0]
    # Encoding: rs=rs, rt=rt(rw), rd=msb=lsb+size-1, sa=lsb=pos
    def ins(rs, rt, pos, size):
        msb = pos + size - 1
        return r_type(rs, rt, msb, pos, 0x04, op=0x1F)

    ins_cases = [
        (1, 3, 0, 1),   # insert bit 0 into rt[0]
        (1, 3, 0, 8),   # insert byte into rt[7:0]
        (1, 3, 8, 8),   # insert byte into rt[15:8]
        (1, 3, 0, 16),  # insert half into rt[15:0]
        (1, 3, 16, 16), # insert half into rt[31:16]
        (1, 3, 4, 4),   # insert nibble at pos 4
        (2, 5, 0, 8),   # r2=0xFFFFFFFF, r5=100
        (4, 5, 16, 8),  # r4=0x7FFFFFFF → insert low8 at pos 16
        (7, 8, 4, 8),   # r7=0x12345678 into r8=0xABCDEF01
        (5, 6, 0, 32),  # replace entire word (pos=0, size=32)
        (1, 3, 31, 1),  # insert at bit 31
    ]
    for rs, rt, pos, size in ins_cases:
        emit("special3", ins(rs, rt, pos, size), BASE_REGS)
    for val_rs, val_rt in [(0, 0xFFFFFFFF), (0xFFFFFFFF, 0), (0x12345678, 0xDEADBEEF)]:
        regs = make_regs(r1=val_rs, r3=val_rt)
        for pos, size in [(0, 8), (8, 8), (0, 16), (16, 16)]:
            emit("special3", ins(1, 3, pos, size), regs)

gen_special3()

# ── BSHFL (SPECIAL3 funct=0x20) ────────────────────────────────────────────

def gen_bshfl():
    def bshfl(rt, rd, sa):   # op=0x1F, funct=0x20
        return r_type(0, rt, rd, sa, 0x20, op=0x1F)
    vals = [0, 1, 0x7F, 0x80, 0xFF, 0x7FFF, 0x8000, 0xFFFF,
            0x12345678, 0xDEADBEEF, 0xABCDEF01, 0x80000000, 0x7FFFFFFF, 0xFFFFFFFF]
    for rt in [1, 2, 3, 4, 7, 8]:
        emit("bshfl", bshfl(rt, 9, 0x10), BASE_REGS)   # SEB
        emit("bshfl", bshfl(rt, 9, 0x18), BASE_REGS)   # SEH
        emit("bshfl", bshfl(rt, 9, 0x02), BASE_REGS)   # WSBH
    for val in vals:
        regs = make_regs(r1=val)
        emit("bshfl", bshfl(1, 3, 0x10), regs)  # SEB
        emit("bshfl", bshfl(1, 3, 0x18), regs)  # SEH
        emit("bshfl", bshfl(1, 3, 0x02), regs)  # WSBH

gen_bshfl()

# ── BRANCH-LIKELY (BEQL/BNEL/BLEZL/BGTZL) ─────────────────────────────────

def gen_branch_likely():
    # Branch-likely doesn't modify GPRs; test that decode doesn't corrupt registers.
    # Use forward offset=0 (branch to PC+4, same as fall-through slot).
    ops = [
        (0x14, "beql"),
        (0x15, "bnel"),
        (0x16, "blezl"),
        (0x17, "bgtzl"),
    ]
    for op, _ in ops:
        for rs in [0, 1, 3, 4, 10]:   # r0=0, r3=INT_MIN, r4=INT_MAX, r10=0, r1=1
            for rt in [0, 1]:
                word = i_type(op, rs, rt, 0)
                emit("branch-likely", word, BASE_REGS)
        for rset in RAND_REGS_SETS[:2]:
            emit("branch-likely", i_type(op, 1, 2, 0), rset)

gen_branch_likely()

# ── CONDITIONAL TRAPS (SPECIAL) ────────────────────────────────────────────
# Only generate NO-TRAP vectors (trap condition false) so Unicorn runs cleanly.
# When condition is false, no GPR/HI/LO changes.

def gen_trap_r():
    # BASE_REGS sampler: r1=1, r5=100, r9=42, r10=0, r23=1, r22=0
    # TGE(0x30) no-trap: rs < rt  → (r1,r5):1<100 ✓  (r9,r5):42<100 ✓
    # TGEU(0x31) no-trap: rs < rt unsigned
    # TLT(0x32) no-trap: rs >= rt → (r5,r9):100>=42 ✓  (r5,r1):100>=1 ✓
    # TLTU(0x33) no-trap: rs >= rt unsigned
    # TEQ(0x34) no-trap: rs != rt → (r1,r5) ✓  (r9,r5) ✓
    # TNE(0x36) no-trap: rs == rt → (r1,r23):1==1 ✓  (r10,r22):0==0 ✓
    notrap = [
        (0x30, 1, 5), (0x30, 9, 5), (0x30, 10, 1),
        (0x31, 1, 5), (0x31, 9, 5), (0x31, 10, 23),
        (0x32, 5, 1), (0x32, 5, 9), (0x32, 9, 9),   # 9>=9 not < → ok wait 42>=42 ✓
        (0x33, 5, 1), (0x33, 5, 9),
        (0x34, 1, 5), (0x34, 9, 5), (0x34, 2, 3),
        (0x36, 1, 23), (0x36, 10, 22), (0x36, 10, 10),  # 0==0 no-trap for TNE
    ]
    for funct, rs, rt in notrap:
        emit("trap-r", r_type(rs, rt, 0, 0, funct), BASE_REGS)
    # Also cover TGE where rs==rt (≥ means TRAP) — skip those
    # Random regs: only TEQ/TNE where equality is unlikely
    for rset in RAND_REGS_SETS[:2]:
        emit("trap-r", r_type(1, 2, 0, 0, 0x34), rset)  # TEQ: r1!=r2 very likely
        emit("trap-r", r_type(1, 1, 0, 0, 0x36), rset)  # TNE: r1==r1 always no-trap

gen_trap_r()

# ── REGIMM TRAPS (TGEI/TGEIU/TLTI/TLTIU/TEQI/TNEI) ───────────────────────

def gen_trap_i():
    # rt field encodes the trap-immediate opcode
    # Only NO-TRAP vectors.
    # r1=1, r5=100, r9=42
    # TGEI(0x08) no-trap: rs < simm → r1=1 < 100 ✓
    # TGEIU(0x09) no-trap: rs < simm unsigned
    # TLTI(0x0A) no-trap: rs >= simm → r5=100 >= 50 ✓
    # TLTIU(0x0B) no-trap: rs >= simm unsigned
    # TEQI(0x0C) no-trap: rs != simm → r1=1, imm=2 ✓
    # TNEI(0x0E) no-trap: rs == simm → r1=1, imm=1 ✓
    notrap = [
        (0x08, 1,  100),  (0x08, 9,  100),  (0x08, 10, 1),
        (0x09, 1,  100),  (0x09, 9,  100),
        (0x0A, 5,  50),   (0x0A, 5,  100),  (0x0A, 9,  42),   # 42>=42 not < ✓
        (0x0B, 5,  50),   (0x0B, 5,  100),
        (0x0C, 1,  2),    (0x0C, 5,  101),  (0x0C, 9,  43),
        (0x0E, 1,  1),    (0x0E, 5,  100),  (0x0E, 9,  42),
    ]
    for rt_op, rs, imm in notrap:
        emit("trap-i", i_type(0x01, rs, rt_op, imm & 0xFFFF), BASE_REGS)
    # Negative immediates (sign-extended): imm=0xFFFF → simm=-1
    for rt_op in [0x08, 0x0C, 0x0E]:
        emit("trap-i", i_type(0x01, 2, rt_op, 0xFFFF), BASE_REGS)  # simm=-1, rs=r2=-1

gen_trap_i()

# ── MEMORY OPERATIONS: helper for data-memory vectors ──────────────────────
#
# Unicorn MIPS translates kseg0 (0x80000000-0x9FFFFFFF) → physical (strip bit 31).
# So the oracle must use a PHYSICAL address (DATA_PHYS = 0x00001000) for data,
# while the SEI checker uses the virtual kseg0 address (DATA_VIRT = 0x80001000).
#
# Each memory vector carries `base_reg` and `mem_virt` so the checker knows
# which register to substitute with the virtual address.

DATA_PHYS = 0x00001000   # physical address in Unicorn flat space
DATA_VIRT = 0x80001000   # virtual kseg0 address in SEI (kseg0: → phys 0x00001000)
MEM_BASE  = 28           # $gp: register holding the data base address

def run_insn_mem(word, in_regs, in_hi=0, in_lo=0, data_word=0):
    """Execute one instruction with a data memory region at DATA_PHYS."""
    mu = Uc(UC_ARCH_MIPS, UC_MODE_MIPS32 + UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE & ~0xFFF, 0x3000)
    mu.mem_map(DATA_PHYS, 0x1000)
    mu.mem_write(CODE, struct.pack('<II', word, 0))   # insn + NOP
    mu.mem_write(DATA_PHYS, struct.pack('<I', data_word & 0xFFFFFFFF))
    for i, v in enumerate(in_regs):
        if i == 0:
            continue
        mu.reg_write(REG0 + i, v & 0xFFFFFFFF)
    mu.reg_write(HI_REG, in_hi & 0xFFFFFFFF)
    mu.reg_write(LO_REG, in_lo & 0xFFFFFFFF)
    try:
        mu.emu_start(CODE, CODE + 0x2000, count=1)
    except UcError:
        return None
    out_regs = [mu.reg_read(REG0 + i) for i in range(32)]
    out_mem = struct.unpack('<I', bytes(mu.mem_read(DATA_PHYS, 4)))[0]
    return (out_regs, mu.reg_read(HI_REG), mu.reg_read(LO_REG), out_mem)

def emit_mem(group, word, in_regs, data_word, in_hi=0, in_lo=0, check_mem=False):
    """Emit a memory vector. in_regs[MEM_BASE] must be DATA_PHYS (oracle physical)."""
    res = run_insn_mem(word, in_regs, in_hi, in_lo, data_word)
    if res is None:
        return
    out_regs, out_hi, out_lo, out_mem = res
    vec = {
        "group": group,
        "insn": word,
        "base_reg": MEM_BASE,
        "mem_virt": DATA_VIRT,
        "in_regs": list(in_regs),
        "in_hi": in_hi,
        "in_lo": in_lo,
        "in_mem_word": data_word & 0xFFFFFFFF,
        "out_regs": out_regs,
        "out_hi": out_hi,
        "out_lo": out_lo,
    }
    if check_mem:
        vec["out_mem_word"] = out_mem
    vectors.append(vec)

def mem_regs(**extra):
    """BASE_REGS with r28 = DATA_PHYS (oracle physical) and optional overrides."""
    r = make_regs(r28=DATA_PHYS)
    for k, v in extra.items():
        r[int(k[1:])] = v & 0xFFFFFFFF
    return r

# ── SUB-WORD LOADS ─────────────────────────────────────────────────────────

def gen_memload():
    DATA_WORDS = [
        0x00000000, 0x12345678, 0xDEADBEEF, 0x80000000,
        0x7FFFFFFF, 0xABCDEF01, 0xFF808100, 0x01020304,
    ]
    for data_word in DATA_WORDS:
        # LB (0x20) and LBU (0x24): test all 4 byte positions
        for offset in [0, 1, 2, 3]:
            emit_mem("memload", i_type(0x20, MEM_BASE, 3, offset), mem_regs(), data_word)   # LB
            emit_mem("memload", i_type(0x24, MEM_BASE, 3, offset), mem_regs(), data_word)   # LBU
        # LH (0x21) and LHU (0x25): halfword at offset 0 or 2
        for offset in [0, 2]:
            emit_mem("memload", i_type(0x21, MEM_BASE, 3, offset), mem_regs(), data_word)   # LH
            emit_mem("memload", i_type(0x25, MEM_BASE, 3, offset), mem_regs(), data_word)   # LHU
    # LWL / LWR: test all 4 byte offsets, initial rt value matters
    for data_word in [0x12345678, 0xDEADBEEF, 0x80000000, 0xFFFFFFFF]:
        for init_rt in [0x00000000, 0xFFFFFFFF, 0xAAAAAAAA]:
            for offset in [0, 1, 2, 3]:
                emit_mem("memload", i_type(0x22, MEM_BASE, 3, offset),  # LWL
                         mem_regs(r3=init_rt), data_word)
                emit_mem("memload", i_type(0x26, MEM_BASE, 3, offset),  # LWR
                         mem_regs(r3=init_rt), data_word)

gen_memload()

# ── SUB-WORD STORES ────────────────────────────────────────────────────────

def gen_memstore():
    DATA_WORDS = [0x00000000, 0xFFFFFFFF, 0xDEADBEEF]
    # SB (0x28): store low byte of rt at each offset
    for data_word in DATA_WORDS:
        for store_reg in [1, 7, 2, 11]:   # r1=1, r7=0x12345678, r2=-1, r11=0xFFFF
            for offset in [0, 1, 2, 3]:
                emit_mem("memstore", i_type(0x28, MEM_BASE, store_reg, offset),
                         mem_regs(), data_word, check_mem=True)
    # SH (0x29): store low halfword at offset 0 or 2
    for data_word in DATA_WORDS:
        for store_reg in [1, 7, 2, 11]:
            for offset in [0, 2]:
                emit_mem("memstore", i_type(0x29, MEM_BASE, store_reg, offset),
                         mem_regs(), data_word, check_mem=True)
    # SWL (0x2A) and SWR (0x2E): test all 4 byte offsets
    for data_word in DATA_WORDS:
        for store_reg in [7, 6, 2]:   # r7=0x12345678, r6=0xDEADBEEF, r2=0xFFFFFFFF
            for offset in [0, 1, 2, 3]:
                emit_mem("memstore", i_type(0x2A, MEM_BASE, store_reg, offset),
                         mem_regs(), data_word, check_mem=True)   # SWL
                emit_mem("memstore", i_type(0x2E, MEM_BASE, store_reg, offset),
                         mem_regs(), data_word, check_mem=True)   # SWR

gen_memstore()

# ── LL / SC ────────────────────────────────────────────────────────────────

def gen_ll_sc():
    # LL (0x30): behaves like LW in single-step oracle (sets LLbit internally)
    for data_word in [0x12345678, 0xDEADBEEF, 0x00000000, 0x80000000, 0xFFFFFFFF]:
        emit_mem("ll-sc", i_type(0x30, MEM_BASE, 3, 0), mem_regs(), data_word)  # LL r3, 0(r28)
    # SC (0x38): in a fresh emulator with no prior LL, LLbit=0 → SC fails (rt=0)
    for store_reg in [7, 1, 2]:
        emit_mem("ll-sc", i_type(0x38, MEM_BASE, store_reg, 0),
                 mem_regs(), 0xABCD1234, check_mem=False)

gen_ll_sc()

# ── SPECIAL2: MADD/MADDU/MSUB/MSUBU ────────────────────────────────────────

def gen_madd():
    ops = [
        (0x00, "madd"),
        (0x01, "maddu"),
        (0x04, "msub"),
        (0x05, "msubu"),
    ]
    # SPECIAL2 R-type: op=0x1C, rs, rt, rd=0, sa=0, funct
    test_pairs = [(1,2), (4,5), (7,8), (3,9), (2,14), (4,15)]  # (rs_reg, rt_reg)
    init_accs = [(0, 0), (0, 100), (0xFFFFFFFF, 0xFFFFFFFF), (0, 0x80000000)]
    for funct, name in ops:
        for rs, rt in test_pairs:
            for in_hi, in_lo in init_accs:
                word = (0x1C << 26) | (rs << 21) | (rt << 16) | funct
                emit(f"madd-{name}", word, BASE_REGS, in_hi, in_lo)
        # Random reg sets
        for rset in RAND_REGS_SETS[:3]:
            word = (0x1C << 26) | (1 << 21) | (2 << 16) | funct
            emit(f"madd-{name}", word, rset, 0, 0)

gen_madd()

# ── REGIMM BRANCH-LIKELY: BLTZL/BGEZL/BLTZALL/BGEZALL + SYNCI ─────────────

def gen_regimm_likely():
    # REGIMM: op=0x01, rs, rt=opcode, offset (use 0 → branch to PC+4=delay slot NOP)
    likely_ops = [
        (0x02, "bltzl",  lambda rs_idx: BASE_REGS[rs_idx]),        # taken if < 0
        (0x03, "bgezl",  lambda rs_idx: BASE_REGS[rs_idx]),        # taken if >= 0
    ]
    # rs indices that give varied sign results
    rs_indices = [1, 2, 3, 4, 10, 5, 9]  # 1=1, 2=-1, 3=INT_MIN, 4=INT_MAX, 10=0, 5=100, 9=42
    for rt_op, name, _ in likely_ops:
        for rs in rs_indices:
            word = i_type(0x01, rs, rt_op, 0)
            emit(f"regimm-{name}", word, BASE_REGS)
        for rset in RAND_REGS_SETS[:2]:
            emit(f"regimm-{name}", i_type(0x01, 1, rt_op, 0), rset)

    # BLTZALL (0x12) / BGEZALL (0x13): always link r31 = PC+8 (like BLTZAL/BGEZAL)
    # Use emit_link to translate r31 from oracle's CODE+8 to SEI's CODE_VIRT+8
    for rt_op, name in [(0x12, "bltzall"), (0x13, "bgezall")]:
        for rs in rs_indices:
            word = i_type(0x01, rs, rt_op, 0)
            emit_link(f"regimm-{name}", word, BASE_REGS)
        for rset in RAND_REGS_SETS[:2]:
            emit_link(f"regimm-{name}", i_type(0x01, 1, rt_op, 0), rset)

    # SYNCI (0x1F): NOP — registers unchanged
    for rs in [0, 1, 4]:
        emit("regimm-synci", i_type(0x01, rs, 0x1F, 0), BASE_REGS)

gen_regimm_likely()

# ── SPECIAL3: RDHWR ────────────────────────────────────────────────────────

def gen_rdhwr():
    # RDHWR: op=SPECIAL3(0x1F), rs=0, rt=dest, rd=hwr_num, funct=0x3B
    # hwr2 (cycle counter) skipped — not deterministic
    hwr_list = [0, 1, 3, 29]  # CPUNum, SYNCI_Step, CCRes, ULR
    for rd in hwr_list:
        for rt_dst in [3, 4, 5]:
            word = (0x1F << 26) | (0 << 21) | (rt_dst << 16) | (rd << 11) | 0x3B
            emit("rdhwr", word, BASE_REGS)

gen_rdhwr()

# ── CACHE / PREF (NOP-class) ────────────────────────────────────────────────

def gen_cache_pref():
    # CACHE (0x2F): op=0x2F, rs=base, op_field=rt, imm=offset — no GPR side effects
    # PREF  (0x33): op=0x33, same fields — no GPR side effects
    for op, name in [(0x2F, "cache"), (0x33, "pref")]:
        for rs in [0, 1]:
            for hint in [0, 1]:
                word = i_type(op, rs, hint, 0)
                emit(f"nop-{name}", word, BASE_REGS)

gen_cache_pref()

# ── CP1 FPU ────────────────────────────────────────────────────────────────

UC_MIPS_F0   = UC_MIPS_REG_F0    # 57
UC_MIPS_FCSR = UC_MIPS_REG_FCSR  # 141

BASE_FPRS = [0] * 32

FP_1_0  = 0x3F800000  # 1.0f
FP_2_0  = 0x40000000  # 2.0f
FP_M1_0 = 0xBF800000  # -1.0f
FP_0_5  = 0x3F000000  # 0.5f
FP_100  = 0x42C80000  # 100.0f
FP_PI   = 0x40490FDB  # ~pi
FP_NEG  = 0xC2C80000  # -100.0f

def make_fprs(**kwargs):
    r = list(BASE_FPRS)
    for k, v in kwargs.items():
        r[int(k[1:])] = v & 0xFFFFFFFF
    return r

def run_insn_fp(word, in_regs, in_fprs=None, in_fcsr=0):
    mu = Uc(UC_ARCH_MIPS, UC_MODE_MIPS32 + UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE & ~0xFFF, 0x3000)
    mu.mem_write(CODE, struct.pack('<II', word, 0))
    for i, v in enumerate(in_regs):
        if i == 0: continue
        mu.reg_write(REG0 + i, v & 0xFFFFFFFF)
    mu.reg_write(HI_REG, 0)
    mu.reg_write(LO_REG, 0)
    if in_fprs is not None:
        for i, v in enumerate(in_fprs):
            mu.reg_write(UC_MIPS_F0 + i, v & 0xFFFFFFFF)
    mu.reg_write(UC_MIPS_FCSR, in_fcsr & 0xFFFFFFFF)
    try:
        mu.emu_start(CODE, CODE + 0x2000, count=1)
    except UcError:
        return None
    out_regs = [mu.reg_read(REG0 + i) for i in range(32)]
    out_fprs = [mu.reg_read(UC_MIPS_F0 + i) for i in range(32)]
    return (out_regs, mu.reg_read(HI_REG), mu.reg_read(LO_REG),
            out_fprs, mu.reg_read(UC_MIPS_FCSR))

def emit_fp(group, word, in_regs=None, in_fprs=None, in_fcsr=0,
            check_fprs=True, check_fcsr=False):
    if in_regs is None:
        in_regs = BASE_REGS
    res = run_insn_fp(word, in_regs, in_fprs, in_fcsr)
    if res is None:
        return
    out_regs, out_hi, out_lo, out_fprs, out_fcsr = res
    vec = {
        "group": group,
        "insn": word,
        "in_regs": list(in_regs),
        "in_hi": 0,
        "in_lo": 0,
        "out_regs": out_regs,
        "out_hi": out_hi,
        "out_lo": out_lo,
    }
    if in_fprs is not None:
        vec["in_fprs"] = list(in_fprs)
    if check_fprs:
        vec["out_fprs"] = out_fprs
    if in_fcsr != 0:
        vec["in_fcr31"] = in_fcsr
    if check_fcsr or in_fcsr != 0:
        vec["out_fcr31"] = out_fcsr
    vectors.append(vec)

def cop1_s(fmt_s, ft, fs, fd, funct):
    return (0x11<<26)|(fmt_s<<21)|(ft<<16)|(fs<<11)|(fd<<6)|funct

def cop1_d(ft, fs, fd, funct):
    return cop1_s(0x11, ft, fs, fd, funct)

def cop1_w(fs, fd, funct):
    return cop1_s(0x14, 0, fs, fd, funct)

def gen_fpu_arith():
    fp_vals = [FP_1_0, FP_2_0, FP_M1_0, FP_0_5, FP_100, FP_PI]
    ops_s = [(0x00,'adds'), (0x01,'subs'), (0x02,'muls'), (0x03,'divs')]
    for funct, name in ops_s:
        for a in fp_vals[:4]:
            for b in fp_vals[:4]:
                fprs = make_fprs(f2=a, f4=b)
                emit_fp(f"fpu-{name}", cop1_s(0x10, 4, 2, 6, funct), in_fprs=fprs)
    for funct, name in [(0x04,'sqrts'), (0x05,'abss'), (0x06,'movs'), (0x07,'negs')]:
        for a in fp_vals:
            if funct == 0x04 and (a & 0x80000000):
                continue  # skip negative inputs for SQRT (NaN payload is impl-defined)
            fprs = make_fprs(f2=a)
            emit_fp(f"fpu-{name}", cop1_s(0x10, 0, 2, 4, funct), in_fprs=fprs)
    # Double-precision: FPR pair (f2=lo, f3=hi)
    fp_d_vals = [
        (0x00000000, 0x3FF00000),  # 1.0
        (0x00000000, 0x40000000),  # 2.0
        (0x00000000, 0xBFF00000),  # -1.0
        (0x00000000, 0x3FE00000),  # 0.5
    ]
    ops_d = [(0x00,'addd'), (0x01,'subd'), (0x02,'muld'), (0x03,'divd')]
    for funct, name in ops_d:
        for (lo_a, hi_a) in fp_d_vals[:3]:
            for (lo_b, hi_b) in fp_d_vals[:3]:
                fprs = make_fprs(f2=lo_a, f3=hi_a, f4=lo_b, f5=hi_b)
                emit_fp(f"fpu-{name}", cop1_d(4, 2, 6, funct), in_fprs=fprs)
    for funct, name in [(0x05,'absd'), (0x06,'movd'), (0x07,'negd'), (0x04,'sqrtd')]:
        for (lo, hi) in fp_d_vals:
            if funct == 0x04 and (hi & 0x80000000):
                continue  # skip negative inputs for SQRT
            fprs = make_fprs(f2=lo, f3=hi)
            emit_fp(f"fpu-{name}", cop1_d(0, 2, 4, funct), in_fprs=fprs)

gen_fpu_arith()

def gen_fpu_convert():
    single_vals = [FP_1_0, FP_2_0, FP_M1_0, FP_100, 0x41F00000,  # 30.0
                   0x40A00000,  # 5.0
                   FP_NEG,
                   0x3DCCCCCD,  # 0.1
                   0xBDCCCCCD,  # -0.1
                   0x3FC00000,  # 1.5
                   0xBFC00000,  # -1.5
                   ]
    for funct, name in [(0x24,'cvtws'), (0x0D,'truncws'), (0x0C,'roundws'),
                        (0x0E,'ceilws'), (0x0F,'floorws')]:
        for v in single_vals:
            fprs = make_fprs(f2=v)
            emit_fp(f"fpu-{name}", cop1_s(0x10, 0, 2, 4, funct), in_fprs=fprs)
    int_vals = [0, 1, 0xFFFFFFFF, 100, 1000000, 0x7FFFFFFF, 0x80000000]
    for iv in int_vals:
        fprs = make_fprs(f2=iv)
        emit_fp("fpu-cvtsw", cop1_w(2, 4, 0x20), in_fprs=fprs)
    for iv in int_vals:
        fprs = make_fprs(f2=iv)
        emit_fp("fpu-cvtdw", cop1_w(2, 4, 0x21), in_fprs=fprs)
    for v in [FP_1_0, FP_2_0, FP_M1_0, FP_PI]:
        fprs = make_fprs(f2=v)
        emit_fp("fpu-cvtds", cop1_s(0x10, 0, 2, 4, 0x21), in_fprs=fprs)
    for (lo, hi) in [(0,0x3FF00000),(0,0x40000000),(0,0xBFF00000)]:
        fprs = make_fprs(f2=lo, f3=hi)
        emit_fp("fpu-cvtsd", cop1_d(0, 2, 4, 0x20), in_fprs=fprs)
    for (lo, hi) in [(0,0x3FF00000),(0,0x40000000),(0,0xBFF00000),(0,0x40590000)]:
        fprs = make_fprs(f2=lo, f3=hi)
        emit_fp("fpu-cvtwd", cop1_d(0, 2, 4, 0x24), in_fprs=fprs)

gen_fpu_convert()

def gen_fpu_cmp():
    fp_pairs = [(FP_1_0, FP_1_0), (FP_1_0, FP_2_0), (FP_2_0, FP_1_0)]
    for cond in range(16):
        funct = 0x30 | cond
        word = cop1_s(0x10, 4, 2, 0, funct)
        for (a, b) in fp_pairs:
            fprs = make_fprs(f2=a, f4=b)
            emit_fp(f"fpu-cconds{cond}", word, in_fprs=fprs, check_fprs=False, check_fcsr=True)
    d_pairs = [
        ((0,0x3FF00000),(0,0x3FF00000)),
        ((0,0x3FF00000),(0,0x40000000)),
        ((0,0x40000000),(0,0x3FF00000)),
    ]
    for cond in [2, 4, 6]:
        funct = 0x30 | cond
        word = cop1_d(4, 2, 0, funct)
        for ((lo_a,hi_a),(lo_b,hi_b)) in d_pairs:
            fprs = make_fprs(f2=lo_a, f3=hi_a, f4=lo_b, f5=hi_b)
            emit_fp(f"fpu-ccondd{cond}", word, in_fprs=fprs, check_fprs=False, check_fcsr=True)

gen_fpu_cmp()

def gen_fpu_move():
    # MFC1 r3, f4: GPR[3] = FPR[4]
    for fpr_val in [FP_1_0, FP_2_0, FP_M1_0, 0xDEADBEEF]:
        fprs = make_fprs(f4=fpr_val)
        word = (0x11<<26)|(0x00<<21)|(3<<16)|(4<<11)|0
        emit_fp("fpu-mfc1", word, in_fprs=fprs, check_fprs=False)
    # MTC1 r3, f4: FPR[4] = GPR[3]
    for gpr_val in [0x3F800000, 0x12345678, 0]:
        regs = make_regs(r3=gpr_val)
        word = (0x11<<26)|(0x04<<21)|(3<<16)|(4<<11)|0
        emit_fp("fpu-mtc1", word, in_regs=regs, in_fprs=list(BASE_FPRS))
    # CFC1 r3, f31: GPR[3] = FCR31
    for fcsr_val in [0, 0x00800000, 0x01000000]:
        word = (0x11<<26)|(0x02<<21)|(3<<16)|(31<<11)|0
        emit_fp("fpu-cfc1", word, in_fcsr=fcsr_val, check_fprs=False, check_fcsr=True)
    # CTC1 r3, f31: FCR31 = GPR[3]
    for gpr_val in [0, 0x00800000]:
        regs = make_regs(r3=gpr_val)
        word = (0x11<<26)|(0x06<<21)|(3<<16)|(31<<11)|0
        emit_fp("fpu-ctc1", word, in_regs=regs, check_fprs=False, check_fcsr=True)

gen_fpu_move()

def gen_fpu_bc():
    # BC1F (tf=0) and BC1T (tf=1): branch offset=0 (no GPR change)
    for tf, name in [(0,'bc1f'), (1,'bc1t')]:
        word = i_type(0x11, 0x08, tf, 0)
        for fcsr in [0, 0x00800000]:
            emit_fp(f"fpu-{name}", word, in_fcsr=fcsr, check_fprs=False)

gen_fpu_bc()

def run_insn_fpmem(word, in_regs, in_fprs=None, data_word=0):
    mu = Uc(UC_ARCH_MIPS, UC_MODE_MIPS32 + UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE & ~0xFFF, 0x3000)
    mu.mem_map(DATA_PHYS, 0x1000)
    mu.mem_write(CODE, struct.pack('<II', word, 0))
    mu.mem_write(DATA_PHYS, struct.pack('<I', data_word & 0xFFFFFFFF))
    for i, v in enumerate(in_regs):
        if i == 0: continue
        mu.reg_write(REG0 + i, v & 0xFFFFFFFF)
    mu.reg_write(HI_REG, 0)
    mu.reg_write(LO_REG, 0)
    if in_fprs:
        for i, v in enumerate(in_fprs):
            mu.reg_write(UC_MIPS_F0 + i, v & 0xFFFFFFFF)
    mu.reg_write(UC_MIPS_FCSR, 0)
    try:
        mu.emu_start(CODE, CODE + 0x2000, count=1)
    except UcError:
        return None
    out_regs = [mu.reg_read(REG0+i) for i in range(32)]
    out_fprs = [mu.reg_read(UC_MIPS_F0+i) for i in range(32)]
    out_mem = struct.unpack('<I', bytes(mu.mem_read(DATA_PHYS, 4)))[0]
    return out_regs, out_fprs, out_mem

def emit_fpmem(group, word, in_regs, in_fprs=None, data_word=0, check_mem=False, check_fprs=True):
    res = run_insn_fpmem(word, in_regs, in_fprs, data_word)
    if res is None: return
    out_regs, out_fprs, out_mem = res
    vec = {
        "group": group,
        "insn": word,
        "base_reg": MEM_BASE,
        "mem_virt": DATA_VIRT,
        "in_regs": list(in_regs),
        "in_hi": 0,
        "in_lo": 0,
        "in_mem_word": data_word & 0xFFFFFFFF,
        "out_regs": out_regs,
        "out_hi": 0,
        "out_lo": 0,
    }
    if in_fprs is not None:
        vec["in_fprs"] = list(in_fprs)
    if check_fprs:
        vec["out_fprs"] = out_fprs
    if check_mem:
        vec["out_mem_word"] = out_mem
    vectors.append(vec)

def gen_fpu_mem():
    for fpr_val in [FP_1_0, FP_2_0, 0, 0xDEADBEEF, 0x80000000]:
        # LWC1 f4, 0(r28): FPR[4] = MEM
        emit_fpmem("fpu-lwc1", i_type(0x31, MEM_BASE, 4, 0), mem_regs(), data_word=fpr_val)
        # SWC1 f4, 0(r28): MEM = FPR[4]
        emit_fpmem("fpu-swc1", i_type(0x39, MEM_BASE, 4, 0), mem_regs(),
                   in_fprs=make_fprs(f4=fpr_val), data_word=0, check_mem=True, check_fprs=False)

gen_fpu_mem()

# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------

output = {
    "arch": "mips32le",
    "oracle": "unicorn",
    "group": "all",
    "vectors": vectors,
}

if len(sys.argv) < 2:
    print(f"Generated {len(vectors)} vectors", file=sys.stderr)
    sys.exit(0)

out_path = sys.argv[1]
with open(out_path, "w") as f:
    json.dump(output, f, separators=(',', ':'))
    f.write('\n')

print(f"Wrote {len(vectors)} vectors to {out_path}", file=sys.stderr)
