#!/usr/bin/env python3
# OFFLINE ORACLE (dev tool, NOT part of the SEI Lean build): generate T16
# (Thumb-1 + ARMv6) golden vectors via Unicorn for the Lean stepThumb decoder.
# Usage: python3 thumb_gen.py > tests/armvec/t16-vectors.json
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *

CODE = 0x10000   # instruction lives here
MEM  = 0x20000   # test memory for load/store

REGS = [UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3,
        UC_ARM_REG_R4,UC_ARM_REG_R5,UC_ARM_REG_R6,UC_ARM_REG_R7,
        UC_ARM_REG_R8,UC_ARM_REG_R9,UC_ARM_REG_R10,UC_ARM_REG_R11,
        UC_ARM_REG_R12,UC_ARM_REG_R13,UC_ARM_REG_R14]

random.seed(0xA16)
def rr(): return random.getrandbits(32)

MEMSIZE = 64
MEM_INIT = bytes(range(MEMSIZE))

def cpsr_nzcv(c): return [(c>>31)&1, (c>>30)&1, (c>>29)&1, (c>>28)&1]

def run_thumb(hw_bytes, in_regs, nzcv, mem_init=None):
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM | UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE, 0x2000)
    mu.mem_map(MEM,  0x1000)
    mu.mem_write(CODE, hw_bytes + b'\x00\x00\x00\x00')
    mu.mem_write(MEM, bytes(mem_init) if mem_init is not None else MEM_INIT)
    for i, r in enumerate(REGS):
        mu.reg_write(r, in_regs[i] & 0xffffffff)
    n,z,c,v = nzcv
    cpsr = (n<<31)|(z<<30)|(c<<29)|(v<<28)|(1<<5)|0x13  # SVC, T=1
    mu.reg_write(UC_ARM_REG_CPSR, cpsr)
    try:
        mu.emu_start(CODE | 1, CODE + len(hw_bytes), count=1)
    except UcError:
        return None
    out = [mu.reg_read(r) & 0xffffffff for r in REGS]
    pc  = mu.reg_read(UC_ARM_REG_PC) & 0xffffffff
    ocpsr = mu.reg_read(UC_ARM_REG_CPSR)
    omem = list(mu.mem_read(MEM, MEMSIZE))
    return out, pc, cpsr_nzcv(ocpsr), omem

def emit(insn_bytes, in_regs, nzcv=(0,0,0,0), group="dp", mem_init=None, label=None):
    r = run_thumb(insn_bytes, in_regs, nzcv, mem_init)
    if r is None: return None
    out_regs, out_pc, out_nzcv, out_mem = r
    d = {"arch": "t16", "group": group, "oracle": "unicorn",
         "insn": list(insn_bytes),
         "in_regs":  [x & 0xffffffff for x in in_regs],
         "in_nzcv":  list(nzcv),
         "out_regs": out_regs, "out_pc": out_pc, "out_nzcv": out_nzcv}
    if mem_init is not None:
        d["mem_base"] = MEM
        d["pre_mem"] = list(mem_init)
        d["post_mem"] = out_mem
    if label: d["label"] = label
    return d

def hw(x): return struct.pack('<H', x & 0xffff)

# ── encoding helpers ──────────────────────────────────────────────────────────
def lsl_imm(rd,rm,i5):  return hw(0x0000|(i5<<6)|(rm<<3)|rd)
def lsr_imm(rd,rm,i5):  return hw(0x0800|(i5<<6)|(rm<<3)|rd)
def asr_imm(rd,rm,i5):  return hw(0x1000|(i5<<6)|(rm<<3)|rd)
def add_reg(rd,rn,rm):  return hw(0x1800|(rm<<6)|(rn<<3)|rd)
def sub_reg(rd,rn,rm):  return hw(0x1A00|(rm<<6)|(rn<<3)|rd)
def add_i3(rd,rn,i):    return hw(0x1C00|(i<<6)|(rn<<3)|rd)
def sub_i3(rd,rn,i):    return hw(0x1E00|(i<<6)|(rn<<3)|rd)
def mov_i8(rd,i):       return hw(0x2000|(rd<<8)|i)
def cmp_i8(rn,i):       return hw(0x2800|(rn<<8)|i)
def add_i8(rd,i):       return hw(0x3000|(rd<<8)|i)
def sub_i8(rd,i):       return hw(0x3800|(rd<<8)|i)
def alu_op(op,rm,rdn):  return hw(0x4000|(op<<6)|(rm<<3)|rdn)
def add_hi(dn,rm):      return hw(0x4400|((dn>>3)<<7)|(rm<<3)|(dn&7))
def cmp_hi(dn,rm):      return hw(0x4500|((dn>>3)<<7)|(rm<<3)|(dn&7))
def mov_hi(dn,rm):      return hw(0x4600|((dn>>3)<<7)|(rm<<3)|(dn&7))
def bx_r(rm):           return hw(0x4700|(rm<<3))
def blx_r(rm):          return hw(0x4780|(rm<<3))
def ldr_lit(rd,i8):     return hw(0x4800|(rd<<8)|i8)
def str_r(rt,rn,rm):    return hw(0x5000|(rm<<6)|(rn<<3)|rt)
def strh_r(rt,rn,rm):   return hw(0x5200|(rm<<6)|(rn<<3)|rt)
def strb_r(rt,rn,rm):   return hw(0x5400|(rm<<6)|(rn<<3)|rt)
def ldrsb_r(rt,rn,rm):  return hw(0x5600|(rm<<6)|(rn<<3)|rt)
def ldr_r(rt,rn,rm):    return hw(0x5800|(rm<<6)|(rn<<3)|rt)
def ldrh_r(rt,rn,rm):   return hw(0x5A00|(rm<<6)|(rn<<3)|rt)
def ldrb_r(rt,rn,rm):   return hw(0x5C00|(rm<<6)|(rn<<3)|rt)
def ldrsh_r(rt,rn,rm):  return hw(0x5E00|(rm<<6)|(rn<<3)|rt)
def str_i(rt,rn,i5):    return hw(0x6000|(i5<<6)|(rn<<3)|rt)
def ldr_i(rt,rn,i5):    return hw(0x6800|(i5<<6)|(rn<<3)|rt)
def strb_i(rt,rn,i5):   return hw(0x7000|(i5<<6)|(rn<<3)|rt)
def ldrb_i(rt,rn,i5):   return hw(0x7800|(i5<<6)|(rn<<3)|rt)
def strh_i(rt,rn,i5):   return hw(0x8000|(i5<<6)|(rn<<3)|rt)
def ldrh_i(rt,rn,i5):   return hw(0x8800|(i5<<6)|(rn<<3)|rt)
def str_sp(rt,i8):       return hw(0x9000|(rt<<8)|i8)
def ldr_sp(rt,i8):       return hw(0x9800|(rt<<8)|i8)
def add_pc_rd(rd,i8):    return hw(0xA000|(rd<<8)|i8)
def add_sp_rd(rd,i8):    return hw(0xA800|(rd<<8)|i8)
def add_sp_sp(i7):       return hw(0xB000|i7)
def sub_sp_sp(i7):       return hw(0xB080|i7)
def sxth(rd,rm):         return hw(0xB200|(rm<<3)|rd)
def sxtb(rd,rm):         return hw(0xB240|(rm<<3)|rd)
def uxth(rd,rm):         return hw(0xB280|(rm<<3)|rd)
def uxtb(rd,rm):         return hw(0xB2C0|(rm<<3)|rd)
def push_r(rlist,lr=0):  return hw(0xB400|(lr<<8)|rlist)
def pop_r(rlist,pc=0):   return hw(0xBC00|(pc<<8)|rlist)
def rev_r(rd,rm):        return hw(0xBA00|(rm<<3)|rd)
def rev16_r(rd,rm):      return hw(0xBA40|(rm<<3)|rd)
def revsh_r(rd,rm):      return hw(0xBAC0|(rm<<3)|rd)
def stmia_r(rn,rlist):   return hw(0xC000|(rn<<8)|rlist)
def ldmia_r(rn,rlist):   return hw(0xC800|(rn<<8)|rlist)
def bcond_r(cond,i8):    return hw(0xD000|(cond<<8)|(i8&0xff))
def b_r(i11):            return hw(0xE000|(i11&0x7ff))
def bl_hw1(imm22):       return hw(0xF000|((imm22>>12)&0x7ff))
def bl_hw2(imm22):       return hw(0xF800|((imm22>>1)&0x7ff))

# base register values (r0-r14): avoid SP=0 crashes; r13=MEM+0x100 as stack
BASE_REGS = [0x11111111,0x22222222,0x33333333,0x44444444,
             0x55555555,0x66666666,0x77777777,0x88888888,
             0x99999999,0xAAAAAAAA,0xBBBBBBBB,0xCCCCCCCC,
             0xDDDDDDDD,MEM+0x100,0xEEEEEEEE]

def regs(**kw):
    r = list(BASE_REGS)
    for k,v in kw.items(): r[int(k[1:])] = v & 0xffffffff
    return r

vecs = []

# ── Group 000: shift immediate ────────────────────────────────────────────────
for (g, fn) in [("lsl_imm", lsl_imm), ("lsr_imm", lsr_imm), ("asr_imm", asr_imm)]:
    for imm5 in [0,1,7,15,31]:
        for nzcv in [(0,0,0,0),(1,0,1,0),(0,1,0,0)]:
            rv = regs(r2=rr(), r3=rr())
            v = emit(fn(2,3,imm5), rv, nzcv, g)
            if v: vecs.append(v)

# add/sub reg
for (g, fn) in [("add_reg",add_reg),("sub_reg",sub_reg)]:
    for nzcv in [(0,0,0,0),(1,1,0,0),(0,0,1,0)]:
        rv = regs(r2=rr(),r3=rr(),r4=rr())
        v = emit(fn(2,3,4), rv, nzcv, g); vecs.append(v) if v else None
        # edge: all-zeros, all-ones
        rv2 = regs(r2=0,r3=0,r4=0)
        v = emit(fn(0,1,2), rv2, (0,0,0,0), g); vecs.append(v) if v else None

# add/sub imm3
for (g, fn) in [("add_i3",add_i3),("sub_i3",sub_i3)]:
    for i in range(8):
        rv = regs(r2=0xDEAD,r3=rr())
        v = emit(fn(2,3,i), rv, (0,0,0,0), g); vecs.append(v) if v else None

# ── Group 001: MOV/CMP/ADD/SUB imm8 ──────────────────────────────────────────
for imm in [0,1,0x7F,0x80,0xFF]:
    for nzcv in [(0,0,0,0),(1,0,1,1)]:
        rv = regs(r0=rr())
        for (g,fn) in [("mov_i8",mov_i8),("cmp_i8",cmp_i8),("add_i8",add_i8),("sub_i8",sub_i8)]:
            v = emit(fn(0,imm), rv, nzcv, g); vecs.append(v) if v else None

# ── Group 010000: ALU ─────────────────────────────────────────────────────────
ALU_OPS = {
    0:"and",1:"eor",2:"lsl_r",3:"lsr_r",4:"asr_r",5:"adc",6:"sbc",7:"ror",
    8:"tst",9:"neg",10:"cmp",11:"cmn",12:"orr",13:"mul",14:"bic",15:"mvn"
}
for op,nm in ALU_OPS.items():
    for _ in range(3):
        rv = regs(r0=rr(),r1=rr())
        nzcv = (random.randint(0,1),random.randint(0,1),random.randint(0,1),random.randint(0,1))
        v = emit(alu_op(op,1,0), rv, nzcv, "alu_"+nm); vecs.append(v) if v else None
    # edge: shift by 0 and 33
    if op in (2,3,4,7):
        for sh in [0,1,8,31,32,33,255]:
            rv = regs(r0=rr(),r1=sh)
            v = emit(alu_op(op,1,0), rv, (0,0,1,0), "alu_"+nm+"_edge"); vecs.append(v) if v else None

# ── Group 010001: high register ops ──────────────────────────────────────────
# MOV high: MOV r8, r1 (reading from low, writing to high)
for src in range(8):
    rv = regs(**{f"r{src}": rr()})
    v = emit(mov_hi(8,src), rv, (0,0,0,0), "mov_hi"); vecs.append(v) if v else None
# ADD high
for _ in range(4):
    rv = regs(r0=rr(),r8=rr())
    v = emit(add_hi(8,0), rv, (0,0,0,0), "add_hi"); vecs.append(v) if v else None
# CMP high
for _ in range(4):
    rv = regs(r0=rr(),r8=rr())
    v = emit(cmp_hi(8,0), rv, (0,0,0,0), "cmp_hi"); vecs.append(v) if v else None

# ── Groups 0101/011/1000/1001: load/store ─────────────────────────────────────
MEMBASE = MEM
MEMOFF  = 4   # use offset 4 in test memory to avoid boundary

def mem_regs(rn_val, rm_val=4):
    r = list(BASE_REGS)
    r[1] = rn_val & 0xffffffff  # Rn = r1 points to memory
    r[2] = rm_val & 0xffffffff  # Rm = r2 = offset
    r[0] = 0xDEADBEEF           # Rt = r0 (for stores)
    return r

# STR/LDR register (r0,[r1,r2])
for (g,fn) in [("str_r",str_r),("ldr_r",ldr_r),("strh_r",strh_r),("ldrh_r",ldrh_r),
               ("strb_r",strb_r),("ldrb_r",ldrb_r),("ldrsb_r",ldrsb_r),("ldrsh_r",ldrsh_r)]:
    rv = mem_regs(MEMBASE+MEMOFF)
    minit = bytearray(MEM_INIT)
    v = emit(fn(0,1,2), rv, (0,0,0,0), g, minit); vecs.append(v) if v else None

# STR/LDR immediate (r0,[r1,#imm5*4])
for imm5 in [0,1,3]:
    for (g,fn) in [("str_i",str_i),("ldr_i",ldr_i)]:
        rv = mem_regs(MEMBASE)
        v = emit(fn(0,1,imm5), rv, (0,0,0,0), g, bytearray(MEM_INIT)); vecs.append(v) if v else None

# STRB/LDRB immediate
for imm5 in [0,1,7]:
    for (g,fn) in [("strb_i",strb_i),("ldrb_i",ldrb_i)]:
        rv = mem_regs(MEMBASE)
        v = emit(fn(0,1,imm5), rv, (0,0,0,0), g, bytearray(MEM_INIT)); vecs.append(v) if v else None

# STRH/LDRH immediate
for imm5 in [0,1,3]:
    for (g,fn) in [("strh_i",strh_i),("ldrh_i",ldrh_i)]:
        rv = mem_regs(MEMBASE)
        v = emit(fn(0,1,imm5), rv, (0,0,0,0), g, bytearray(MEM_INIT)); vecs.append(v) if v else None

# SP-relative load/store (r3,[SP,#imm8*4]) where SP=MEM+0x100
for imm8 in [0,1,4]:
    for (g,fn) in [("str_sp",str_sp),("ldr_sp",ldr_sp)]:
        rv = list(BASE_REGS)
        rv[13] = MEMBASE  # set SP to MEM base
        rv[3]  = 0xBEEFCAFE
        v = emit(fn(3,imm8), rv, (0,0,0,0), g, bytearray(MEM_INIT)); vecs.append(v) if v else None

# ── Group 1010: ADD Rd, PC/SP, #imm ──────────────────────────────────────────
for imm8 in [0,1,4,63]:
    rv = list(BASE_REGS); rv[13] = 0x8000
    v = emit(add_pc_rd(0,imm8), rv, (0,0,0,0), "add_pc"); vecs.append(v) if v else None
    v = emit(add_sp_rd(0,imm8), rv, (0,0,0,0), "add_sp"); vecs.append(v) if v else None

# ── Group 1011: Misc ──────────────────────────────────────────────────────────
# ADD/SUB SP
for imm7 in [0,1,4,0x7f]:
    rv = list(BASE_REGS); rv[13] = 0x8000
    v = emit(add_sp_sp(imm7), rv, (0,0,0,0), "add_sp_sp"); vecs.append(v) if v else None
    v = emit(sub_sp_sp(imm7), rv, (0,0,0,0), "sub_sp_sp"); vecs.append(v) if v else None

# ARMv6 sign/zero extend
for val in [0xFF, 0x7F, 0x80FF, 0x8001, 0xFFFFFFFF]:
    rv = list(BASE_REGS); rv[1] = val
    for (g,fn) in [("sxth",sxth),("sxtb",sxtb),("uxth",uxth),("uxtb",uxtb)]:
        v = emit(fn(0,1), rv, (0,0,0,0), g); vecs.append(v) if v else None

# PUSH / POP  (uses stack region at MEM+0x100)
for rlist in [0x01, 0x0F, 0x55, 0xFF]:
    rv = list(BASE_REGS); rv[13] = MEMBASE + 0x100
    v = emit(push_r(rlist,lr=0), rv, (0,0,0,0), "push", bytearray(MEM_INIT+(b'\x00'*(256+4-len(MEM_INIT)))))
    if v: vecs.append(v)
    v = emit(push_r(rlist,lr=1), rv, (0,0,0,0), "push_lr", bytearray(MEM_INIT+(b'\x00'*(256+4-len(MEM_INIT)))))
    if v: vecs.append(v)

# POP (load from stack)
for rlist in [0x01, 0x0F, 0x55]:
    rv = list(BASE_REGS); rv[13] = MEMBASE
    v = emit(pop_r(rlist,pc=0), rv, (0,0,0,0), "pop", bytearray(MEM_INIT))
    if v: vecs.append(v)

# REV / REV16 / REVSH
for val in [0x12345678, 0xDEADBEEF, 0x00FF00FF, 0xFF000000]:
    rv = list(BASE_REGS); rv[1] = val
    for (g,fn) in [("rev",rev_r),("rev16",rev16_r),("revsh",revsh_r)]:
        v = emit(fn(0,1), rv, (0,0,0,0), g); vecs.append(v) if v else None

# ── Group 1100: STMIA / LDMIA ────────────────────────────────────────────────
for rlist in [0x07, 0x0F, 0x55, 0xFF]:
    rv = list(BASE_REGS); rv[0] = MEMBASE
    v = emit(stmia_r(0,rlist), rv, (0,0,0,0), "stmia", bytearray(MEM_INIT)); vecs.append(v) if v else None
    rv[0] = MEMBASE
    v = emit(ldmia_r(0,rlist), rv, (0,0,0,0), "ldmia", bytearray(MEM_INIT)); vecs.append(v) if v else None

# ── Group 1101: conditional branch ───────────────────────────────────────────
# Branch taken and not-taken for each condition
for cond in range(14):
    for nzcv in [(0,0,0,0),(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(1,1,1,1)]:
        rv = list(BASE_REGS)
        # offset 2 forward (imm8=1 → offset = 2+4=6 from pc... wait)
        # bcond imm8=1: offset = signext(1)*2 = 2, target = pc+4+2 = CODE+6
        v = emit(bcond_r(cond,1), rv, nzcv, "bcond"); vecs.append(v) if v else None
        # backward branch (imm8=0xFE = -2 → offset=-4, target=pc+4-4=pc)
        # self-branch (haltOnSelfBranch would catch this, so skip)

# ── Group 11100: unconditional branch ────────────────────────────────────────
# Forward and backward (skip self-branch)
for i11 in [1, 5, 0x7FE]:
    v = emit(b_r(i11), list(BASE_REGS), (0,0,0,0), "b_uncond"); vecs.append(v) if v else None
# Backward
for i11 in [0x7FF]:  # -1 in 11-bit → target = pc+4 + (-2) = pc+2 (next instr... actually pc)
    # i11=0x7FF → signext11(0x7FF) = -1 → offset = -2, target = pc+4-2 = pc+2
    # That's a tight loop to the second halfword of a non-existent 4-byte insn at pc.
    # Let's use i11=0x7FD → -3 → offset=-6, target=pc+4-6=pc-2 (valid backward)
    pass
v = emit(b_r(0x7FD), list(BASE_REGS), (0,0,0,0), "b_backward"); vecs.append(v) if v else None

# ── BL (32-bit two-halfword) ──────────────────────────────────────────────────
# BL #8: offset from pc+4 = 8, imm22 = 8
# First hw: F000 | (8>>12 & 7FF) = F000 | 0 = F000
# Second hw: F800 | (8>>1 & 7FF) = F800 | 4 = F804
# Target = (CODE+4) + 8 = CODE+12 = 0x1000C
def bl_pair(offset22):
    hw1 = 0xF000 | ((offset22 >> 12) & 0x7FF)
    hw2 = 0xF800 | ((offset22 >> 1)  & 0x7FF)
    return struct.pack('<HH', hw1, hw2)

for off in [8, 16, -4]:
    off22 = off & 0x3FFFFF  # mask to 22 bits (signed)
    rv = list(BASE_REGS)
    result = run_thumb(bl_pair(off22), rv, (0,0,0,0))
    if result:
        out_r, out_pc, out_nzcv, _ = result
        vecs.append({"arch":"t16","group":"bl","oracle":"unicorn",
                     "insn": list(bl_pair(off22)),
                     "in_regs": rv, "in_nzcv": [0,0,0,0],
                     "out_regs": out_r, "out_pc": out_pc, "out_nzcv": out_nzcv,
                     "label": f"bl_off_{off}"})

# ── CBZ / CBNZ ────────────────────────────────────────────────────────────
def cbz_w(Rn, offset, is_nz):
    """offset in bytes from PC+4, must be 0..126, even. CBZ=0, CBNZ=1."""
    i = (offset >> 6) & 1
    imm5 = (offset >> 1) & 0x1f
    op_bit = 0x08 if is_nz else 0x00
    return struct.pack('<H', 0xB100 | op_bit | (i<<9) | (imm5<<3) | (Rn&7))

BASE_REGS_CBZ = [0x11111111,0x22222222,0x33333333,0x44444444,
                  0x55555555,0x66666666,0x77777777,0x88888888,
                  0x99999999,0xAAAAAAAA,0xBBBBBBBB,0xCCCCCCCC,
                  0xDDDDDDDD,MEM+0x100,0xEEEEEEEE]

for rn_val, off in [(0, 4), (0, 16), (1, 4), (0x11111111, 4)]:
    rv = list(BASE_REGS_CBZ); rv[0] = rn_val
    v = emit(cbz_w(0, off, False), rv, (0,0,0,0), "cbz", label=f"cbz_r0={rn_val}_off={off}")
    if v: vecs.append(v)
    v = emit(cbz_w(0, off, True),  rv, (0,0,0,0), "cbnz", label=f"cbnz_r0={rn_val}_off={off}")
    if v: vecs.append(v)

# ── WFI / WFE / SEV (hint NOPs) ───────────────────────────────────────────
for hint_byte, label in [(0x20, "wfe"), (0x30, "wfi"), (0x40, "sev"), (0x00, "nop")]:
    rv = list(BASE_REGS_CBZ)
    insn = struct.pack('<H', 0xBF00 | hint_byte)
    v = emit(insn, rv, (0,0,0,0), label)
    if v: vecs.append(v)

# ── BX / BLX register (010001 op=11) ─────────────────────────────────────────
# Target must be a valid Thumb address (bit 0 = 1) to stay in Thumb mode.
# Use r2 and r3 as branch targets pointing into a Thumb-mapped region.
# Unicorn executes count=1 instruction and stops; only PC/LR state matters.
for rm_idx in [2, 3, 5]:
    rv = list(BASE_REGS)
    rv[rm_idx] = CODE + 8 + 1  # Thumb target (CODE+8, Thumb bit set)
    v = emit(bx_r(rm_idx), rv, (0,0,0,0), "bx_r", label=f"bx_r{rm_idx}")
    if v: vecs.append(v)
    v = emit(blx_r(rm_idx), rv, (0,0,0,0), "blx_r", label=f"blx_r{rm_idx}")
    if v: vecs.append(v)

# BX to ARM mode (bit 0 = 0): switches tbit to false
for rm_idx in [4, 6]:
    rv = list(BASE_REGS)
    rv[rm_idx] = CODE + 8  # ARM target (bit 0 = 0)
    v = emit(bx_r(rm_idx), rv, (0,0,0,0), "bx_arm", label=f"bx_r{rm_idx}_arm")
    if v: vecs.append(v)

# ── LDR (literal / PC-relative) ───────────────────────────────────────────────
# addr = pcR + imm8*4 where pcR = CODE+4; data at CODE+4..CODE+4+255*4 is zero.
# Load returns 0; tests that the correct rd gets 0.
for rd_t in [0, 2, 4, 7]:
    for i8 in [0, 1, 4]:
        rv = list(BASE_REGS)
        v = emit(ldr_lit(rd_t, i8), rv, (0,0,0,0), "ldr_lit", label=f"ldr_lit_r{rd_t}_i{i8}")
        if v: vecs.append(v)

# ── Load/Store with varied Rt (expose register field coverage) ─────────────────
for Rt_t in [1, 3, 5, 7]:
    rv = list(BASE_REGS)
    rv[1] = MEMBASE + MEMOFF  # Rn
    rv[2] = 0                  # Rm = 0 for zero offset
    rv[Rt_t] = 0xAABBCCDD     # src value for stores
    minit = bytearray(MEM_INIT)
    for (g, fn) in [("str_r_rt", str_r), ("ldr_r_rt", ldr_r),
                    ("strb_r_rt", strb_r), ("ldrb_r_rt", ldrb_r),
                    ("strh_r_rt", strh_r), ("ldrh_r_rt", ldrh_r)]:
        v = emit(fn(Rt_t, 1, 2), rv, (0,0,0,0), g, minit)
        if v: vecs.append(v)
    # Immediate-offset forms (imm5=0 to stay in bounds)
    for (g2, fn2) in [("str_i_rt", str_i), ("ldr_i_rt", ldr_i),
                      ("strb_i_rt", strb_i), ("ldrb_i_rt", ldrb_i),
                      ("strh_i_rt", strh_i), ("ldrh_i_rt", ldrh_i)]:
        rv2 = list(rv); rv2[1] = MEMBASE
        v = emit(fn2(Rt_t, 1, 0), rv2, (0,0,0,0), g2, bytearray(MEM_INIT))
        if v: vecs.append(v)

print(json.dumps({"arch":"t16","group":"mixed","oracle":"unicorn+Unicorn-2.0",
                  "vectors": [v for v in vecs if v]}, indent=1))
print(f"Generated {len([v for v in vecs if v])} vectors", file=sys.stderr)
