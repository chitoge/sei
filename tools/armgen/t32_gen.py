#!/usr/bin/env python3
# OFFLINE ORACLE (dev tool): generate T32 (Thumb-2 32-bit) golden vectors via Unicorn.
# Usage: python3 t32_gen.py > tests/armvec/t32-vectors.json
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *

CODE = 0x10000
MEM  = 0x20000

REGS = [UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3,
        UC_ARM_REG_R4,UC_ARM_REG_R5,UC_ARM_REG_R6,UC_ARM_REG_R7,
        UC_ARM_REG_R8,UC_ARM_REG_R9,UC_ARM_REG_R10,UC_ARM_REG_R11,
        UC_ARM_REG_R12,UC_ARM_REG_R13,UC_ARM_REG_R14]

random.seed(0xA32)
def rr(): return random.getrandbits(32)

MEMSIZE = 64
MEM_INIT = bytes(range(MEMSIZE))
BASE_REGS = [0x11111111,0x22222222,0x33333333,0x44444444,
             0x55555555,0x66666666,0x77777777,0x88888888,
             0x99999999,0xAAAAAAAA,0xBBBBBBBB,0xCCCCCCCC,
             0xDDDDDDDD,MEM+0x100,0xEEEEEEEE]

def cpsr_nzcv(c): return [(c>>31)&1,(c>>30)&1,(c>>29)&1,(c>>28)&1]

def run_t32(insn_bytes, in_regs, nzcv, mem_init=None):
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM | UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE, 0x2000)
    mu.mem_map(MEM,  0x1000)
    mu.mem_write(CODE, bytes(insn_bytes) + b'\x00\x00\x00\x00')
    mu.mem_write(MEM, bytes(mem_init) if mem_init else MEM_INIT)
    for i, r in enumerate(REGS): mu.reg_write(r, in_regs[i] & 0xffffffff)
    n,z,c,v = nzcv
    cpsr = (n<<31)|(z<<30)|(c<<29)|(v<<28)|(1<<5)|0x13
    mu.reg_write(UC_ARM_REG_CPSR, cpsr)
    try:
        mu.emu_start(CODE | 1, CODE + 4, count=1)
    except UcError:
        return None
    out = [mu.reg_read(r) & 0xffffffff for r in REGS]
    pc  = mu.reg_read(UC_ARM_REG_PC) & 0xffffffff
    ocpsr = mu.reg_read(UC_ARM_REG_CPSR)
    omem = list(mu.mem_read(MEM, MEMSIZE))
    return out, pc, cpsr_nzcv(ocpsr), omem

def t32(hw1, hw2):
    return struct.pack('<HH', hw1 & 0xffff, hw2 & 0xffff)

def emit(hw1, hw2, in_regs, nzcv=(0,0,0,0), group="t32", mem_init=None, label=None):
    b = t32(hw1, hw2)
    r = run_t32(b, in_regs, nzcv, mem_init)
    if r is None: return None
    out_regs, out_pc, out_nzcv, out_mem = r
    d = {"arch":"t32","group":group,"oracle":"unicorn",
         "insn": list(b),
         "in_regs": [x & 0xffffffff for x in in_regs],
         "in_nzcv": list(nzcv),
         "out_regs": out_regs, "out_pc": out_pc, "out_nzcv": out_nzcv}
    if mem_init is not None:
        d["mem_base"] = MEM
        d["pre_mem"] = list(mem_init)
        d["post_mem"] = out_mem
    if label: d["label"] = label
    return d

def regs(**kw):
    r = list(BASE_REGS)
    for k,v in kw.items(): r[int(k[1:])] = v & 0xffffffff
    return r

# ── encoding helpers ──────────────────────────────────────────────────────────
# T32 DP modified immediate: hw1 = 0xF000 | (i<<10) | (op<<5) | (S<<4) | Rn
# imm12 = (i<<11)|(imm3<<8)|imm8; hw2 = (imm3<<12)|(Rd<<8)|imm8
DP_IMM_OPS = {  # op→(opcode, name)
    "and":0x0,"bic":0x1,"orr":0x2,"orn":0x3,"eor":0x4,
    "add":0x8,"adc":0xA,"sbc":0xB,"sub":0xD,"rsb":0xE }

def dp_imm(op, S, Rn, Rd, imm12):
    i    = (imm12 >> 11) & 1
    imm3 = (imm12 >>  8) & 7
    imm8 = imm12 & 0xff
    hw1  = 0xF000 | (i<<10) | (op<<5) | (S<<4) | (Rn&0xf)
    hw2  = (imm3<<12) | ((Rd&0xf)<<8) | imm8
    return hw1, hw2

# T32 DP shifted register: hw1 = 0xEA00 | (op<<5) | (S<<4) | Rn
# hw2 = (imm3<<12)|(Rd<<8)|(imm2<<6)|(stype<<4)|Rm; shift=(imm3<<2)|imm2
def dp_reg(op, S, Rn, Rd, Rm, stype=0, shift=0):
    imm3 = (shift >> 2) & 7
    imm2 = shift & 3
    hw1  = 0xEA00 | (op<<5) | (S<<4) | (Rn&0xf)
    hw2  = (imm3<<12) | ((Rd&0xf)<<8) | (imm2<<6) | ((stype&3)<<4) | (Rm&0xf)
    return hw1, hw2

# MOVW T3: hw1 = 0xF240|(i<<10)|imm4, hw2=(imm3<<12)|(Rd<<8)|imm8
def movw(Rd, imm16):
    i = (imm16>>11)&1; imm4=(imm16>>12)&0xf; imm3=(imm16>>8)&7; imm8=imm16&0xff
    return 0xF240|(i<<10)|imm4, (imm3<<12)|((Rd&0xf)<<8)|imm8

# MOVT T1: hw1 = 0xF2C0|(i<<10)|imm4, hw2=(imm3<<12)|(Rd<<8)|imm8
def movt(Rd, imm16):
    i=(imm16>>11)&1; imm4=(imm16>>12)&0xf; imm3=(imm16>>8)&7; imm8=imm16&0xff
    return 0xF2C0|(i<<10)|imm4, (imm3<<12)|((Rd&0xf)<<8)|imm8

# ADDW T4: add Rd, Rn, #imm12 (no flags); hw1=0xF200|(i<<10)|Rn, hw2=(imm3<<12)|(Rd<<8)|imm8
def addw(Rd, Rn, imm12):
    i=(imm12>>11)&1; imm3=(imm12>>8)&7; imm8=imm12&0xff
    return 0xF200|(i<<10)|(Rn&0xf), (imm3<<12)|((Rd&0xf)<<8)|imm8

# SUBW T4: sub Rd, Rn, #imm12 (no flags)
def subw(Rd, Rn, imm12):
    i=(imm12>>11)&1; imm3=(imm12>>8)&7; imm8=imm12&0xff
    return 0xF2A0|(i<<10)|(Rn&0xf), (imm3<<12)|((Rd&0xf)<<8)|imm8

# SBFX T1: sbfx Rd, Rn, #lsb, #width
# hw1=0xF340|Rn, hw2=(lsb_hi<<12)|(Rd<<8)|(lsb_lo<<6)|((width-1)&0x1f)
def sbfx(Rd, Rn, lsb, width):
    imm3=(lsb>>2)&7; imm2=lsb&3
    return 0xF340|(Rn&0xf), (imm3<<12)|((Rd&0xf)<<8)|(imm2<<6)|((width-1)&0x1f)

# UBFX T1: ubfx Rd, Rn, #lsb, #width
def ubfx(Rd, Rn, lsb, width):
    imm3=(lsb>>2)&7; imm2=lsb&3
    return 0xF3C0|(Rn&0xf), (imm3<<12)|((Rd&0xf)<<8)|(imm2<<6)|((width-1)&0x1f)

# BFI T1: bfi Rd, Rn, #lsb, #width  (hw1 = 0xF360|Rn, Rn≠1111)
def bfi(Rd, Rn, lsb, width):
    msb = lsb + width - 1
    imm3=(lsb>>2)&7; imm2=lsb&3
    return 0xF360|(Rn&0xf), (imm3<<12)|((Rd&0xf)<<8)|(imm2<<6)|(msb&0x1f)

# LDR.W T3 (positive imm12): ldr Rt,[Rn,#imm12]
def ldr_w(Rt, Rn, imm12):  return 0xF8D0|(Rn&0xf), ((Rt&0xf)<<12)|(imm12&0xfff)
def str_w(Rt, Rn, imm12):  return 0xF8C0|(Rn&0xf), ((Rt&0xf)<<12)|(imm12&0xfff)
def ldrb_w(Rt,Rn,imm12):   return 0xF890|(Rn&0xf), ((Rt&0xf)<<12)|(imm12&0xfff)
def strb_w(Rt,Rn,imm12):   return 0xF880|(Rn&0xf), ((Rt&0xf)<<12)|(imm12&0xfff)
def ldrh_w(Rt,Rn,imm12):   return 0xF8B0|(Rn&0xf), ((Rt&0xf)<<12)|(imm12&0xfff)
def strh_w(Rt,Rn,imm12):   return 0xF8A0|(Rn&0xf), ((Rt&0xf)<<12)|(imm12&0xfff)
def ldrsb_w(Rt,Rn,imm12):  return 0xF990|(Rn&0xf), ((Rt&0xf)<<12)|(imm12&0xfff)
def ldrsh_w(Rt,Rn,imm12):  return 0xF9B0|(Rn&0xf), ((Rt&0xf)<<12)|(imm12&0xfff)

# LDR register T2: ldr Rt,[Rn,Rm,LSL #shift]
def ldr_r(Rt,Rn,Rm,shift=0):  return 0xF850|(Rn&0xf), ((Rt&0xf)<<12)|(shift<<4)|(Rm&0xf)
def str_r(Rt,Rn,Rm,shift=0):  return 0xF840|(Rn&0xf), ((Rt&0xf)<<12)|(shift<<4)|(Rm&0xf)
def ldrb_r(Rt,Rn,Rm,shift=0): return 0xF810|(Rn&0xf), ((Rt&0xf)<<12)|(shift<<4)|(Rm&0xf)
def strb_r(Rt,Rn,Rm,shift=0): return 0xF800|(Rn&0xf), ((Rt&0xf)<<12)|(shift<<4)|(Rm&0xf)
def ldrh_r(Rt,Rn,Rm,shift=0): return 0xF830|(Rn&0xf), ((Rt&0xf)<<12)|(shift<<4)|(Rm&0xf)
def strh_r(Rt,Rn,Rm,shift=0): return 0xF820|(Rn&0xf), ((Rt&0xf)<<12)|(shift<<4)|(Rm&0xf)

# LDRD T1 (offset): ldrd Rt,Rt2,[Rn,#imm8*4] (U=1 add)
def ldrd(Rt,Rt2,Rn,imm8): return 0xE9D0|(Rn&0xf), ((Rt&0xf)<<12)|((Rt2&0xf)<<8)|(imm8&0xff)
def strd(Rt,Rt2,Rn,imm8): return 0xE9C0|(Rn&0xf), ((Rt&0xf)<<12)|((Rt2&0xf)<<8)|(imm8&0xff)

# LDMIA.W (T2) with writeback: ldmia.w Rn!,{regs}
def ldmia_w(Rn, rlist): return 0xE8B0|(Rn&0xf), rlist&0xdfff
def stmia_w(Rn, rlist): return 0xE8A0|(Rn&0xf), rlist&0x5fff
# LDMDB.W (T1) with writeback: ldmdb Rn!,{regs}
def ldmdb_w(Rn, rlist): return 0xE930|(Rn&0xf), rlist&0xdfff
def stmdb_w(Rn, rlist): return 0xE920|(Rn&0xf), rlist&0x5fff

# MUL T2: mul Rd, Rn, Rm
def mul_w(Rd, Rn, Rm): return 0xFB00|(Rn&0xf), ((Rd&0xf)<<8)|0x00F0|(Rm&0xf)
# MLA T1: mla Rd, Rn, Rm, Ra
def mla_w(Rd,Rn,Rm,Ra): return 0xFB00|(Rn&0xf), ((Ra&0xf)<<12)|((Rd&0xf)<<8)|(Rm&0xf)
# MLS T1: mls Rd, Rn, Rm, Ra
def mls_w(Rd,Rn,Rm,Ra): return 0xFB00|(Rn&0xf), ((Ra&0xf)<<12)|((Rd&0xf)<<8)|0x10|(Rm&0xf)
# SMULL T1: smull RdLo,RdHi,Rn,Rm
def smull_w(RdLo,RdHi,Rn,Rm): return 0xFB80|(Rn&0xf), ((RdLo&0xf)<<12)|((RdHi&0xf)<<8)|(Rm&0xf)
# UMULL T1: umull RdLo,RdHi,Rn,Rm
def umull_w(RdLo,RdHi,Rn,Rm): return 0xFBA0|(Rn&0xf), ((RdLo&0xf)<<12)|((RdHi&0xf)<<8)|(Rm&0xf)
# SMLAL T1: smlal RdLo,RdHi,Rn,Rm
def smlal_w(RdLo,RdHi,Rn,Rm): return 0xFBC0|(Rn&0xf), ((RdLo&0xf)<<12)|((RdHi&0xf)<<8)|(Rm&0xf)
# UMLAL T1: umlal RdLo,RdHi,Rn,Rm
def umlal_w(RdLo,RdHi,Rn,Rm): return 0xFBE0|(Rn&0xf), ((RdLo&0xf)<<12)|((RdHi&0xf)<<8)|(Rm&0xf)
# SDIV T1: sdiv Rd,Rn,Rm
def sdiv_w(Rd,Rn,Rm): return 0xFB90|(Rn&0xf), ((Rd&0xf)<<8)|0x00F0|(Rm&0xf)
# UDIV T1: udiv Rd,Rn,Rm
def udiv_w(Rd,Rn,Rm): return 0xFBB0|(Rn&0xf), ((Rd&0xf)<<8)|0x00F0|(Rm&0xf)
# CLZ T1: clz Rd, Rm
def clz_w(Rd,Rm): return 0xFAB0|(Rm&0xf), ((Rd&0xf)<<8)|0x0820|(Rm&0xf)
# MRS T1 (read CPSR→Rd): hw1=0xF3EF, Rd at hw2[11:8], hw2[15:13]=100
def mrs_cpsr(Rd): return 0xF3EF, ((Rd&0xf)<<8)|0x8000
# NOP.W T2
def nop_w(): return 0xF3AF, 0x8000

# B.W T4 (unconditional, 25-bit signed offset): encodes I1/I2 as per ARMv7
def b_w(offset):  # offset in bytes from pc+4
    S  = 1 if offset < 0 else 0
    off25 = offset & 0x1FFFFFF
    I1 = (off25 >> 23) & 1; I2 = (off25 >> 22) & 1
    J1 = int(not (I1 ^ S)); J2 = int(not (I2 ^ S))
    imm10 = (off25 >> 12) & 0x3FF; imm11 = (off25 >> 1) & 0x7FF
    return 0xF000|((S)<<10)|imm10, 0x9000|(J1<<13)|(J2<<11)|imm11

# B.W T3 (conditional, 21-bit signed offset)
def bcond_w(cond, offset):  # offset in bytes from pc+4
    S = 1 if offset < 0 else 0
    off21 = offset & 0x1FFFFF
    J1 = (off21 >> 19) & 1; J2 = (off21 >> 18) & 1
    imm6 = (off21 >> 12) & 0x3F; imm11 = (off21 >> 1) & 0x7FF
    return 0xF000|((S)<<10)|((cond&0xf)<<6)|imm6, 0x8000|(J1<<13)|(J2<<11)|imm11

# ── test imm12 patterns (thumbExpandImm representation) ──────────────────────
# Pattern: 0x00ab = ZeroExtend(0xab); 0x01ab = ab00ab00; 0x02ab = ab000ab0...
# Using simple values that are valid for modified-immediate encoding
IMM12_VALS = [0x000,0x001,0x007F,0x0FF,0x100,0x1FF,0x200,0x400,0x500,0x5A5]

vecs = []

# ── DP modified immediate ─────────────────────────────────────────────────────
for nm, op in DP_IMM_OPS.items():
    for imm12 in [0x00F, 0x0FF, 0x101, 0x201, 0x412]:
        for nzcv in [(0,0,0,0),(1,0,1,0),(0,1,0,0)]:
            rv = regs(r0=rr(),r1=rr())
            # S=1 variants (set flags)
            v = emit(*dp_imm(op,1,1,0,imm12), rv, nzcv, "dp_imm_"+nm+"s")
            if v: vecs.append(v)
            # S=0 (no flags) for non-CMP ops
            if nm not in ("tst","teq","cmp","cmn"):
                v = emit(*dp_imm(op,0,1,0,imm12), rv, nzcv, "dp_imm_"+nm)
                if v: vecs.append(v)
    # Varied Rd, Rn to exercise register fields
    if nm not in ("tst","teq","cmp","cmn"):
        for Rd_t, Rn_t in [(3,2),(5,4)]:
            rv = regs(**{f'r{Rn_t}': rr(), f'r{Rd_t}': rr()})
            v = emit(*dp_imm(op,0,Rn_t,Rd_t,0x0FF), rv, (0,0,0,0), "dp_imm_"+nm+"_rd")
            if v: vecs.append(v)
    # MOV immediate (Rn=1111, op=orr): MOV Rd,#imm12
    for imm12 in [0x00F, 0x0FF, 0x412]:
        rv = regs()
        v = emit(*dp_imm(0x2,1,0xf,0,imm12), rv, (0,0,0,0), "mov_imm")
        if v: vecs.append(v)
    # MVN immediate (Rn=1111, op=orn)
    if nm == "orn":
        for imm12 in [0x00F, 0x0FF]:
            rv = regs()
            v = emit(*dp_imm(0x3,1,0xf,0,imm12), rv, (0,0,0,0), "mvn_imm")
            if v: vecs.append(v)
    # TST (op=and, S=1, Rd=1111)
    if nm == "and":
        for imm12 in [0x00F, 0x0FF]:
            rv = regs(r1=rr())
            v = emit(*dp_imm(0x0,1,1,0xf,imm12), rv, (0,0,0,0), "tst_imm")
            if v: vecs.append(v)
    # CMP (op=sub, S=1, Rd=1111)
    if nm == "sub":
        for imm12 in [0x00F, 0x0FF, 0x100]:
            rv = regs(r1=rr())
            v = emit(*dp_imm(0xD,1,1,0xf,imm12), rv, (0,0,0,0), "cmp_imm")
            if v: vecs.append(v)
    # CMN (op=add, S=1, Rd=1111)
    if nm == "add":
        for imm12 in [0x00F, 0x0FF]:
            rv = regs(r1=rr())
            v = emit(*dp_imm(0x8,1,1,0xf,imm12), rv, (0,0,0,0), "cmn_imm")
            if v: vecs.append(v)

# ── DP shifted register ───────────────────────────────────────────────────────
SHIFTS = [(0,0),(0,1),(0,7),(1,1),(2,1),(3,4)]  # (stype, shift_amt)
for nm, op in DP_IMM_OPS.items():
    for stype,sh in SHIFTS:
        rv = regs(r0=rr(),r1=rr(),r2=rr())
        v = emit(*dp_reg(op,1,1,0,2,stype,sh), rv, (0,0,1,0), "dp_reg_"+nm)
        if v: vecs.append(v)
    # Varied Rd, Rn, Rm
    if nm not in ("tst","teq","cmp","cmn"):
        for Rd_t, Rn_t, Rm_t in [(3,4,5),(6,2,7)]:
            rv = regs(**{f'r{Rn_t}': rr(), f'r{Rm_t}': rr(), f'r{Rd_t}': rr()})
            v = emit(*dp_reg(op,0,Rn_t,Rd_t,Rm_t,0,0), rv, (0,0,0,0), "dp_reg_"+nm+"_rd")
            if v: vecs.append(v)
    # MOV register (Rn=1111) with shift  = MOV.W Rd,Rm,LSL #sh
    for stype,sh in [(0,0),(0,1),(1,2),(2,3),(3,4)]:
        rv = regs(r2=rr())
        v = emit(*dp_reg(0x2,1,0xf,0,2,stype,sh), rv, (0,0,1,0), "mov_reg_shift")
        if v: vecs.append(v)
    # TST.W (op=and, S=1, Rd=1111)
    if nm == "and":
        rv = regs(r0=rr(),r1=rr())
        v = emit(*dp_reg(0x0,1,0,0xf,1,0,0), rv, (0,0,0,0), "tst_reg")
        if v: vecs.append(v)
    # CMP.W (op=sub, S=1, Rd=1111)
    if nm == "sub":
        rv = regs(r0=rr(),r1=rr())
        v = emit(*dp_reg(0xD,1,0,0xf,1,0,0), rv, (0,0,0,0), "cmp_reg")
        if v: vecs.append(v)
    # ADC/SBC with carry flag variants
    if nm in ("adc","sbc"):
        for nzcv in [(0,0,0,0),(0,0,1,0),(1,0,1,1)]:
            rv = regs(r0=rr(),r1=rr(),r2=rr())
            v = emit(*dp_reg(op,1,1,0,2,0,0), rv, nzcv, "dp_reg_"+nm)
            if v: vecs.append(v)

# ── MOVW / MOVT ───────────────────────────────────────────────────────────────
for imm16 in [0x0000,0x0001,0x00FF,0x1234,0xABCD,0xFFFF,0x8000]:
    rv = regs(r0=rr())
    v = emit(*movw(0,imm16), rv, (0,0,0,0), "movw", label=f"movw_{imm16:#06x}")
    if v: vecs.append(v)
    v = emit(*movt(0,imm16), rv, (0,0,0,0), "movt", label=f"movt_{imm16:#06x}")
    if v: vecs.append(v)

# ── ADDW / SUBW ───────────────────────────────────────────────────────────────
for imm12 in [0,1,0xFF,0x100,0x7FF,0xFFF]:
    rv = regs(r0=rr(),r1=rr())
    v = emit(*addw(0,1,imm12), rv, (0,0,0,0), "addw"); vecs.append(v) if v else None
    v = emit(*subw(0,1,imm12), rv, (0,0,0,0), "subw"); vecs.append(v) if v else None
# ADDW/SUBW with varied Rd and Rn to exercise register field decoding
for Rd_t, Rn_t in [(3,2),(5,4),(7,6)]:
    rv = regs(**{f'r{Rn_t}': rr()})
    v = emit(*addw(Rd_t,Rn_t,0x100), rv, (0,0,0,0), "addw_rd"); vecs.append(v) if v else None
    v = emit(*subw(Rd_t,Rn_t,0x80), rv, (0,0,0,0), "subw_rd"); vecs.append(v) if v else None

# ── SBFX / UBFX ──────────────────────────────────────────────────────────────
for (lsb,width) in [(0,8),(8,8),(0,16),(16,16),(24,8),(1,7),(4,12)]:
    rv = regs(r1=rr())
    v = emit(*sbfx(0,1,lsb,width), rv, (0,0,0,0), "sbfx"); vecs.append(v) if v else None
    v = emit(*ubfx(0,1,lsb,width), rv, (0,0,0,0), "ubfx"); vecs.append(v) if v else None

# ── BFI ───────────────────────────────────────────────────────────────────────
for (lsb,width) in [(0,8),(8,8),(0,16),(16,8)]:
    rv = regs(r0=rr(),r1=rr())
    v = emit(*bfi(0,1,lsb,width), rv, (0,0,0,0), "bfi"); vecs.append(v) if v else None

# ── Load/Store single (imm12) ─────────────────────────────────────────────────
LSBASE = MEM
for off in [0,4,8,16,32]:
    rv = regs(r1=LSBASE,r0=0xDEADBEEF)
    mem = bytearray(MEM_INIT)
    # STR.W
    v = emit(*str_w(0,1,off), rv, (0,0,0,0), "str_w", mem); vecs.append(v) if v else None
    # LDR.W
    v = emit(*ldr_w(0,1,off), rv, (0,0,0,0), "ldr_w", mem); vecs.append(v) if v else None
    # STRB.W/LDRB.W
    v = emit(*strb_w(0,1,off), rv, (0,0,0,0), "strb_w", mem); vecs.append(v) if v else None
    v = emit(*ldrb_w(0,1,off), rv, (0,0,0,0), "ldrb_w", mem); vecs.append(v) if v else None
    # STRH.W/LDRH.W
    if off % 2 == 0:
        v = emit(*strh_w(0,1,off), rv, (0,0,0,0), "strh_w", mem); vecs.append(v) if v else None
        v = emit(*ldrh_w(0,1,off), rv, (0,0,0,0), "ldrh_w", mem); vecs.append(v) if v else None
    # Signed extensions
    v = emit(*ldrsb_w(0,1,off), rv, (0,0,0,0), "ldrsb_w", mem); vecs.append(v) if v else None
    if off % 2 == 0:
        v = emit(*ldrsh_w(0,1,off), rv, (0,0,0,0), "ldrsh_w", mem); vecs.append(v) if v else None

# ── Load/Store register offset ────────────────────────────────────────────────
for shift in [0,1,2]:
    rv = regs(r1=LSBASE,r2=4,r0=0xCAFEBABE)
    mem = bytearray(MEM_INIT)
    v = emit(*str_r(0,1,2,shift), rv, (0,0,0,0), "str_r", mem); vecs.append(v) if v else None
    v = emit(*ldr_r(0,1,2,shift), rv, (0,0,0,0), "ldr_r", mem); vecs.append(v) if v else None
    v = emit(*strb_r(0,1,2,shift), rv, (0,0,0,0), "strb_r", mem); vecs.append(v) if v else None
    v = emit(*ldrb_r(0,1,2,shift), rv, (0,0,0,0), "ldrb_r", mem); vecs.append(v) if v else None
    v = emit(*strh_r(0,1,2,shift), rv, (0,0,0,0), "strh_r", mem); vecs.append(v) if v else None
    v = emit(*ldrh_r(0,1,2,shift), rv, (0,0,0,0), "ldrh_r", mem); vecs.append(v) if v else None

# ── LDRD / STRD ───────────────────────────────────────────────────────────────
for imm8 in [0,1,4,8]:
    rv = regs(r2=LSBASE,r0=0x11223344,r1=0x55667788)
    mem = bytearray(MEM_INIT + b'\x00'*(32-len(MEM_INIT)) if len(MEM_INIT)<32 else MEM_INIT)
    v = emit(*strd(0,1,2,imm8), rv, (0,0,0,0), "strd", mem); vecs.append(v) if v else None
    v = emit(*ldrd(0,1,2,imm8), rv, (0,0,0,0), "ldrd", mem); vecs.append(v) if v else None

# ── LDM.W / STM.W ────────────────────────────────────────────────────────────
# Original: Rn=3, rlists avoid bit 3 so writeback is well-defined
for rlist in [0x07,0x0F,0x55,0xFF,0x03FF]:
    rv = regs(r3=LSBASE)
    mem = bytearray(MEM_INIT)
    v = emit(*stmia_w(3,rlist), rv, (0,0,0,0), "stmia_w", mem); vecs.append(v) if v else None
    rv2 = regs(r3=LSBASE)
    v = emit(*ldmia_w(3,rlist), rv2, (0,0,0,0), "ldmia_w", mem); vecs.append(v) if v else None
    rv3 = regs(r3=LSBASE+0x40)
    v = emit(*stmdb_w(3,rlist), rv3, (0,0,0,0), "stmdb_w", mem); vecs.append(v) if v else None
    rv4 = regs(r3=LSBASE+0x40)
    v = emit(*ldmdb_w(3,rlist), rv4, (0,0,0,0), "ldmdb_w", mem); vecs.append(v) if v else None
# Extra: varied Rn (r1, r5) with rlists that exclude the base register
for (rn, rl_base, rl_wide) in [(1, 0xEC, 0x3EC), (5, 0xCF, 0x1CF)]:
    for rlist in [rl_base, rl_wide]:
        rv = regs(**{f'r{rn}': LSBASE})
        mem = bytearray(MEM_INIT)
        v = emit(*stmia_w(rn,rlist), rv, (0,0,0,0), "stmia_w", mem); vecs.append(v) if v else None
        rv2 = regs(**{f'r{rn}': LSBASE})
        v = emit(*ldmia_w(rn,rlist), rv2, (0,0,0,0), "ldmia_w", mem); vecs.append(v) if v else None
        rv3 = regs(**{f'r{rn}': LSBASE+0x40})
        v = emit(*stmdb_w(rn,rlist), rv3, (0,0,0,0), "stmdb_w", mem); vecs.append(v) if v else None
        rv4 = regs(**{f'r{rn}': LSBASE+0x40})
        v = emit(*ldmdb_w(rn,rlist), rv4, (0,0,0,0), "ldmdb_w", mem); vecs.append(v) if v else None

# ── MUL / MLA / MLS ──────────────────────────────────────────────────────────
for _ in range(6):
    rv = regs(r0=rr(),r1=rr(),r2=rr(),r3=rr())
    v = emit(*mul_w(0,1,2), rv, (0,0,0,0), "mul_w"); vecs.append(v) if v else None
    v = emit(*mla_w(0,1,2,3), rv, (0,0,0,0), "mla_w"); vecs.append(v) if v else None
    v = emit(*mls_w(0,1,2,3), rv, (0,0,0,0), "mls_w"); vecs.append(v) if v else None
# edge: multiply by zero, by 1, overflow
for a,b in [(0,0),(1,0xFFFFFFFF),(0xFFFF,0x10000),(0x80000000,2)]:
    rv = regs(r1=a,r2=b)
    v = emit(*mul_w(0,1,2), rv, (0,0,0,0), "mul_edge"); vecs.append(v) if v else None

# ── SMULL / UMULL / SMLAL / UMLAL ────────────────────────────────────────────
for _ in range(5):
    rv = regs(r0=rr(),r1=rr(),r2=rr(),r3=rr())
    v = emit(*smull_w(0,1,2,3), rv, (0,0,0,0), "smull"); vecs.append(v) if v else None
    v = emit(*umull_w(0,1,2,3), rv, (0,0,0,0), "umull"); vecs.append(v) if v else None
    v = emit(*smlal_w(0,1,2,3), rv, (0,0,0,0), "smlal"); vecs.append(v) if v else None
    v = emit(*umlal_w(0,1,2,3), rv, (0,0,0,0), "umlal"); vecs.append(v) if v else None
# overflow case: large values
for a,b in [(0x7FFFFFFF,0x7FFFFFFF),(0xFFFFFFFF,0xFFFFFFFF),(0x80000000,0x80000000)]:
    rv = regs(r0=0,r1=0,r2=a,r3=b)
    v = emit(*smull_w(0,1,2,3), rv, (0,0,0,0), "smull_edge"); vecs.append(v) if v else None
    v = emit(*umull_w(0,1,2,3), rv, (0,0,0,0), "umull_edge"); vecs.append(v) if v else None

# ── SDIV / UDIV ───────────────────────────────────────────────────────────────
for (a,b) in [(10,3),(100,7),(0xFFFFFFFF,2),(0x80000000,1),(0,5),(5,0),(1,1)]:
    rv = regs(r1=a,r2=b)
    v = emit(*sdiv_w(0,1,2), rv, (0,0,0,0), "sdiv"); vecs.append(v) if v else None
    v = emit(*udiv_w(0,1,2), rv, (0,0,0,0), "udiv"); vecs.append(v) if v else None
# signed: negative values
for (a,b) in [(-10,3),(10,-3),(-10,-3),(-1,2),(0x80000000,0xFFFFFFFF)]:
    rv = regs(r1=a & 0xffffffff, r2=b & 0xffffffff)
    v = emit(*sdiv_w(0,1,2), rv, (0,0,0,0), "sdiv_signed"); vecs.append(v) if v else None

# ── CLZ ───────────────────────────────────────────────────────────────────────
for val in [0,1,2,0x80,0xFF,0x8000,0xFFFF,0x80000000,0xFFFFFFFF,0x40000000]:
    rv = regs(r1=val)
    v = emit(*clz_w(0,1), rv, (0,0,0,0), "clz"); vecs.append(v) if v else None

# ── MRS ───────────────────────────────────────────────────────────────────────
for nzcv in [(0,0,0,0),(1,0,1,0),(0,1,0,1),(1,1,1,1)]:
    rv = regs()
    v = emit(*mrs_cpsr(0), rv, nzcv, "mrs_cpsr"); vecs.append(v) if v else None
# MRS with varied Rd to exercise hw2[11:8] register field
for Rd_t in [2, 4, 7]:
    rv = regs()
    v = emit(*mrs_cpsr(Rd_t), rv, (1,0,1,0), "mrs_cpsr_rd"); vecs.append(v) if v else None

# ── NOP.W ─────────────────────────────────────────────────────────────────────
rv = regs()
v = emit(*nop_w(), rv, (0,0,0,0), "nop_w"); vecs.append(v) if v else None

# ── B.W T4 (unconditional) ────────────────────────────────────────────────────
for off in [4, 8, 16, 100, -4, -8]:
    rv = regs()
    v = emit(*b_w(off), rv, (0,0,0,0), "b_w", label=f"b_off_{off}")
    if v: vecs.append(v)

# ── B.W T3 (conditional) ─────────────────────────────────────────────────────
for cond in range(14):
    for nzcv in [(0,0,0,0),(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(1,1,1,1)]:
        rv = regs()
        v = emit(*bcond_w(cond,4), rv, nzcv, "bcond_w"); vecs.append(v) if v else None

# ── TEQ (EOR S=1, Rd=15, no destination write) ───────────────────────────
for imm12 in [0x00F, 0x0FF, 0x412, 0x201]:
    rv = regs(r1=rr())
    v = emit(*dp_imm(0x4,1,1,0xf,imm12), rv, (0,0,0,0), "teq_imm")
    if v: vecs.append(v)
for stype,sh in [(0,0),(0,4),(1,2),(2,3)]:
    rv = regs(r0=rr(),r1=rr())
    v = emit(*dp_reg(0x4,1,0,0xf,1,stype,sh), rv, (0,0,0,0), "teq_reg")
    if v: vecs.append(v)

# ── BL.W T1 ───────────────────────────────────────────────────────────────
def bl_w(offset):
    S = 1 if offset < 0 else 0
    off25 = offset & 0x1FFFFFF
    I1 = (off25 >> 23) & 1; I2 = (off25 >> 22) & 1
    J1 = int(not (I1 ^ S)); J2 = int(not (I2 ^ S))
    imm10 = (off25 >> 12) & 0x3FF; imm11 = (off25 >> 1) & 0x7FF
    return 0xF000|((S)<<10)|imm10, 0xD000|(J1<<13)|(J2<<11)|imm11

for off in [4, 8, 100, -4, -8]:
    rv = regs()
    v = emit(*bl_w(off), rv, (0,0,0,0), "bl_w", label=f"bl_off_{off}")
    if v: vecs.append(v)

# ── LDREX / STREX ─────────────────────────────────────────────────────────
def ldrex_w(Rt, Rn, imm8=0): return 0xE850|(Rn&0xf), ((Rt&0xf)<<12)|0x0F00|(imm8&0xff)
def strex_w(Rd, Rt, Rn, imm8=0): return 0xE840|(Rn&0xf), ((Rt&0xf)<<12)|((Rd&0xf)<<8)|(imm8&0xff)

for off8 in [0, 1, 4]:
    rv = regs(r2=MEM, r0=0xCAFEBABE)
    mem = bytearray(MEM_INIT)
    # STREX: result→r3, source=r0, base=r2
    v = emit(*strex_w(3,0,2,off8), rv, (0,0,0,0), "strex_w", mem)
    if v: vecs.append(v)
    # LDREX: dest=r0, base=r2
    rv2 = regs(r2=MEM)
    v = emit(*ldrex_w(0,2,off8), rv2, (0,0,0,0), "ldrex_w", mem)
    if v: vecs.append(v)

# ── SSAT / USAT ───────────────────────────────────────────────────────────
def ssat_w(Rd, Rn, satN, sh=0, shAmt=0):
    imm3 = (shAmt >> 2) & 7; imm2 = shAmt & 3
    hw1 = 0xF300 | (sh << 5) | (Rn & 0xf)
    hw2 = (imm3 << 12) | ((Rd & 0xf) << 8) | (imm2 << 6) | (satN & 0x1f)
    return hw1, hw2

def usat_w(Rd, Rn, satW, sh=0, shAmt=0):
    imm3 = (shAmt >> 2) & 7; imm2 = shAmt & 3
    hw1 = 0xF380 | (sh << 5) | (Rn & 0xf)
    hw2 = (imm3 << 12) | ((Rd & 0xf) << 8) | (imm2 << 6) | (satW & 0x1f)
    return hw1, hw2

for val, satN in [(0x7FFF, 15), (0x10000, 15), (-1, 8), (0x80000000, 31), (5, 3), (0xFF, 7)]:
    rv = regs(r1=val & 0xffffffff)
    v = emit(*ssat_w(0,1,satN), rv, (0,0,0,0), "ssat_lsl0")
    if v: vecs.append(v)
    v = emit(*ssat_w(0,1,satN,sh=1,shAmt=1), rv, (0,0,0,0), "ssat_asr1")
    if v: vecs.append(v)
for val, satN, sh, shAmt in [(0x100,8,0,2),(0xFFFFFFFF,16,1,1),(0x7F,4,0,1),(0x80000000,31,1,4)]:
    rv = regs(r1=val & 0xffffffff)
    v = emit(*ssat_w(0,1,satN,sh,shAmt), rv, (0,0,0,0), "ssat_shift")
    if v: vecs.append(v)
for val, satW in [(0x7FFF, 15), (0x10000, 15), (-1, 8), (0x80000000, 31), (5, 3)]:
    rv = regs(r1=val & 0xffffffff)
    v = emit(*usat_w(0,1,satW), rv, (0,0,0,0), "usat_lsl0")
    if v: vecs.append(v)
    v = emit(*usat_w(0,1,satW,sh=1,shAmt=1), rv, (0,0,0,0), "usat_asr1")
    if v: vecs.append(v)

# ── Extend-with-rotate (0xFAxx) ───────────────────────────────────────────
def ext_w(op, Rd, Rn, Rm, rot_sel=0):
    """op: 0=SXTH,1=UXTH,2=SXTB16,3=UXTB16,4=SXTB,5=UXTB; Rn=0xf for non-add form."""
    hw1 = 0xFA00 | (op << 4) | (Rn & 0xf)
    hw2 = 0xF080 | ((Rd & 0xf) << 8) | ((rot_sel & 3) << 4) | (Rm & 0xf)
    return hw1, hw2

for rot_sel in [0, 1, 2, 3]:
    rv = regs(r1=rr())
    v = emit(*ext_w(0,0,0xf,1,rot_sel), rv, (0,0,0,0), "sxth_w"); vecs.append(v) if v else None
    v = emit(*ext_w(1,0,0xf,1,rot_sel), rv, (0,0,0,0), "uxth_w"); vecs.append(v) if v else None
    v = emit(*ext_w(4,0,0xf,1,rot_sel), rv, (0,0,0,0), "sxtb_w"); vecs.append(v) if v else None
    v = emit(*ext_w(5,0,0xf,1,rot_sel), rv, (0,0,0,0), "uxtb_w"); vecs.append(v) if v else None
# add variants (Rn!=0xf)
for rot_sel in [0, 1]:
    rv = regs(r0=rr(),r1=rr())
    v = emit(*ext_w(0,2,0,1,rot_sel), rv, (0,0,0,0), "sxtah_w"); vecs.append(v) if v else None
    v = emit(*ext_w(1,2,0,1,rot_sel), rv, (0,0,0,0), "uxtah_w"); vecs.append(v) if v else None
    v = emit(*ext_w(4,2,0,1,rot_sel), rv, (0,0,0,0), "sxtab_w"); vecs.append(v) if v else None
    v = emit(*ext_w(5,2,0,1,rot_sel), rv, (0,0,0,0), "uxtab_w"); vecs.append(v) if v else None
# SXTB16 / UXTB16
for rot_sel in [0, 2]:
    rv = regs(r1=rr())
    v = emit(*ext_w(2,0,0xf,1,rot_sel), rv, (0,0,0,0), "sxtb16_w"); vecs.append(v) if v else None
    v = emit(*ext_w(3,0,0xf,1,rot_sel), rv, (0,0,0,0), "uxtb16_w"); vecs.append(v) if v else None
# with interesting byte patterns
for val in [0xAABBCCDD, 0x80FF7F01, 0xFFFFFFFF, 0x00FF00FF]:
    rv = regs(r1=val)
    v = emit(*ext_w(4,0,0xf,1,0), rv, (0,0,0,0), "sxtb_vals"); vecs.append(v) if v else None
    v = emit(*ext_w(0,0,0xf,1,0), rv, (0,0,0,0), "sxth_vals"); vecs.append(v) if v else None

# ── LDR/STR T4 (pre/post-index with writeback, W=1) ─────────────────────
def ldr_t4(Rt, Rn, imm8, P=1, U=1, W=1):
    puw = (P<<2)|(U<<1)|W
    return 0xF850|(Rn&0xf), ((Rt&0xf)<<12)|0x0800|(puw<<8)|(imm8&0xff)

def str_t4(Rt, Rn, imm8, P=1, U=1, W=1):
    puw = (P<<2)|(U<<1)|W
    return 0xF840|(Rn&0xf), ((Rt&0xf)<<12)|0x0800|(puw<<8)|(imm8&0xff)

for off8 in [0, 4, 8]:
    rv = regs(r1=MEM, r0=0xDEADC0DE)
    mem = bytearray(MEM_INIT)
    v = emit(*str_t4(0,1,off8), rv, (0,0,0,0), "str_t4", mem); vecs.append(v) if v else None
    rv2 = regs(r1=MEM)
    v = emit(*ldr_t4(0,1,off8), rv2, (0,0,0,0), "ldr_t4", mem); vecs.append(v) if v else None
for off8 in [4, 8]:
    rv = regs(r1=MEM, r0=0xBEEFCAFE)
    mem = bytearray(MEM_INIT)
    v = emit(*str_t4(0,1,off8,P=0,U=1,W=1), rv, (0,0,0,0), "str_t4_post", mem); vecs.append(v) if v else None
    rv2 = regs(r1=MEM)
    v = emit(*ldr_t4(0,1,off8,P=0,U=1,W=1), rv2, (0,0,0,0), "ldr_t4_post", mem); vecs.append(v) if v else None

# ── MUL T2 with Ra=0xF (true MUL, not MLA) ───────────────────────────────
def mul_true(Rd, Rn, Rm): return 0xFB00|(Rn&0xf), 0xF000|((Rd&0xf)<<8)|(Rm&0xf)

for _ in range(5):
    rv = regs(r0=rr(),r1=rr(),r2=rr())
    v = emit(*mul_true(0,1,2), rv, (0,0,0,0), "mul_true"); vecs.append(v) if v else None
for a,b in [(0,1),(1,0xFFFFFFFF),(0x10000,0x10000),(0x80000000,2)]:
    rv = regs(r1=a,r2=b)
    v = emit(*mul_true(0,1,2), rv, (0,0,0,0), "mul_true_edge"); vecs.append(v) if v else None

# ── Load/Store single: varied Rt (expose Rd=hw2[11:8] vs Rt=hw2[15:12] bug) ──
# T3 imm12 with Rt != 0; also imm12 >= 0x100 with Rt=0 (imm12[11:8] ≠ 0)
for Rt_t in [2, 3, 5]:
    for off in [0, 8, 16]:
        rv = regs(r1=LSBASE, **{f'r{Rt_t}': 0xDEADBEEF})
        mem = bytearray(MEM_INIT)
        v = emit(*str_w(Rt_t,1,off), rv, (0,0,0,0), "str_w_rt", mem)
        if v: vecs.append(v)
        v = emit(*ldr_w(Rt_t,1,off), rv, (0,0,0,0), "ldr_w_rt", mem)
        if v: vecs.append(v)
        v = emit(*strb_w(Rt_t,1,off), rv, (0,0,0,0), "strb_w_rt", mem)
        if v: vecs.append(v)
        v = emit(*ldrb_w(Rt_t,1,off), rv, (0,0,0,0), "ldrb_w_rt", mem)
        if v: vecs.append(v)
        if off % 2 == 0:
            v = emit(*strh_w(Rt_t,1,off), rv, (0,0,0,0), "strh_w_rt", mem)
            if v: vecs.append(v)
            v = emit(*ldrh_w(Rt_t,1,off), rv, (0,0,0,0), "ldrh_w_rt", mem)
            if v: vecs.append(v)
        v = emit(*ldrsb_w(Rt_t,1,off), rv, (0,0,0,0), "ldrsb_w_rt", mem)
        if v: vecs.append(v)
        if off % 2 == 0:
            v = emit(*ldrsh_w(Rt_t,1,off), rv, (0,0,0,0), "ldrsh_w_rt", mem)
            if v: vecs.append(v)

# imm12 >= 0x100 with Rt=0 (imm12[11:8] ≠ 0 → Rd = wrong register if buggy)
for off in [0x100, 0x200, 0x10]:
    rv = regs(r1=LSBASE, r0=0xCAFEBABE)
    mem = bytearray(MEM_INIT)
    v = emit(*str_w(0,1,off), rv, (0,0,0,0), "str_w_imm12h", mem)
    if v: vecs.append(v)
    v = emit(*ldr_w(0,1,off), rv, (0,0,0,0), "ldr_w_imm12h", mem)
    if v: vecs.append(v)

# T2 register form with Rt != 0
for Rt_t in [2, 4, 6]:
    rv = regs(r1=LSBASE, r3=4, **{f'r{Rt_t}': 0xBEEFCAFE})
    mem = bytearray(MEM_INIT)
    v = emit(*str_r(Rt_t,1,3,0), rv, (0,0,0,0), "str_r_rt", mem)
    if v: vecs.append(v)
    v = emit(*ldr_r(Rt_t,1,3,0), rv, (0,0,0,0), "ldr_r_rt", mem)
    if v: vecs.append(v)
    v = emit(*strb_r(Rt_t,1,3,1), rv, (0,0,0,0), "strb_r_rt", mem)
    if v: vecs.append(v)
    v = emit(*ldrb_r(Rt_t,1,3,1), rv, (0,0,0,0), "ldrb_r_rt", mem)
    if v: vecs.append(v)
    v = emit(*strh_r(Rt_t,1,3,1), rv, (0,0,0,0), "strh_r_rt", mem)
    if v: vecs.append(v)
    v = emit(*ldrh_r(Rt_t,1,3,1), rv, (0,0,0,0), "ldrh_r_rt", mem)
    if v: vecs.append(v)

# STRB/LDRB T4 (8-bit PUW) with Rt != 0 and writeback
def ldrb_t4(Rt, Rn, imm8, P=1, U=1, W=0):
    return 0xF810|(Rn&0xf), ((Rt&0xf)<<12)|0x0800|(P<<10)|(U<<9)|(W<<8)|(imm8&0xff)
def strb_t4(Rt, Rn, imm8, P=1, U=1, W=0):
    return 0xF800|(Rn&0xf), ((Rt&0xf)<<12)|0x0800|(P<<10)|(U<<9)|(W<<8)|(imm8&0xff)
def ldrh_t4(Rt, Rn, imm8, P=1, U=1, W=0):
    return 0xF830|(Rn&0xf), ((Rt&0xf)<<12)|0x0800|(P<<10)|(U<<9)|(W<<8)|(imm8&0xff)
def strh_t4(Rt, Rn, imm8, P=1, U=1, W=0):
    return 0xF820|(Rn&0xf), ((Rt&0xf)<<12)|0x0800|(P<<10)|(U<<9)|(W<<8)|(imm8&0xff)

for Rt_t in [2, 5]:
    for off8 in [0, 8]:
        rv = regs(r1=LSBASE, **{f'r{Rt_t}': 0xAABBCCDD})
        mem = bytearray(MEM_INIT)
        # pre-indexed, no writeback (P=1, U=1, W=0)
        v = emit(*strb_t4(Rt_t,1,off8,P=1,U=1,W=0), rv, (0,0,0,0), "strb_t4_rt", mem)
        if v: vecs.append(v)
        v = emit(*ldrb_t4(Rt_t,1,off8,P=1,U=1,W=0), rv, (0,0,0,0), "ldrb_t4_rt", mem)
        if v: vecs.append(v)
        if off8 % 2 == 0:
            v = emit(*strh_t4(Rt_t,1,off8,P=1,U=1,W=0), rv, (0,0,0,0), "strh_t4_rt", mem)
            if v: vecs.append(v)
            v = emit(*ldrh_t4(Rt_t,1,off8,P=1,U=1,W=0), rv, (0,0,0,0), "ldrh_t4_rt", mem)
            if v: vecs.append(v)
    # pre-indexed with writeback (P=1, U=1, W=1)
    rv = regs(r1=LSBASE, **{f'r{Rt_t}': 0xDEADBABE})
    mem = bytearray(MEM_INIT)
    v = emit(*ldrb_t4(Rt_t,1,4,P=1,U=1,W=1), rv, (0,0,0,0), "ldrb_t4_wb", mem)
    if v: vecs.append(v)
    v = emit(*strb_t4(Rt_t,1,4,P=1,U=1,W=1), rv, (0,0,0,0), "strb_t4_wb", mem)
    if v: vecs.append(v)
    if Rt_t % 2 == 0:
        v = emit(*ldrh_t4(Rt_t,1,4,P=1,U=1,W=1), rv, (0,0,0,0), "ldrh_t4_wb", mem)
        if v: vecs.append(v)
        v = emit(*strh_t4(Rt_t,1,4,P=1,U=1,W=1), rv, (0,0,0,0), "strh_t4_wb", mem)
        if v: vecs.append(v)
    # post-indexed with writeback (P=0, U=1, W=1)
    rv = regs(r1=LSBASE, **{f'r{Rt_t}': 0xFEEDC0DE})
    mem = bytearray(MEM_INIT)
    v = emit(*ldrb_t4(Rt_t,1,8,P=0,U=1,W=1), rv, (0,0,0,0), "ldrb_t4_post", mem)
    if v: vecs.append(v)
    v = emit(*strb_t4(Rt_t,1,8,P=0,U=1,W=1), rv, (0,0,0,0), "strb_t4_post", mem)
    if v: vecs.append(v)

print(json.dumps({"arch":"t32","group":"mixed","oracle":"unicorn",
                  "vectors": [v for v in vecs if v]}, indent=1))
print(f"Generated {len([v for v in vecs if v])} vectors", file=sys.stderr)
