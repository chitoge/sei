#!/usr/bin/env python3
"""Oracle for saturating-narrow ops: VQMOVN.s, VQMOVUN, VQMOVN.u, VQSHRN.s, VQSHRUN, VQSHRN.u.
Generates targeted vectors with negative / overflow edge-case inputs.
Run: python3 narrow_sat_oracle.py tests/armvec/a32-narrow-sat-vectors.json
"""
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *

random.seed(0xBEEF)
CODE = 0x10000
SREGN = [UC_ARM_REG_S0 + i for i in range(32)]

def run(word, sregs_32):
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM)
    mu.mem_map(CODE, 0x1000)
    mu.reg_write(UC_ARM_REG_C1_C0_2, 0x00f00000)
    mu.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    mu.reg_write(UC_ARM_REG_FPSCR, 0)
    mu.mem_write(CODE, struct.pack('<I', word))
    for i, v in enumerate(sregs_32):
        mu.reg_write(SREGN[i], v & 0xffffffff)
    mu.reg_write(UC_ARM_REG_CPSR, 0x13)
    try:
        mu.emu_start(CODE, CODE + 4, count=1)
    except UcError:
        return None
    return [mu.reg_read(SREGN[i]) & 0xffffffff for i in range(32)]

def emit(word, sregs_32):
    outs = run(word, sregs_32)
    if outs is None:
        return None
    return {"insn": word, "in_regs": [0]*15, "in_nzcv": [0,0,0,0],
            "in_sregs": sregs_32,
            "out_regs": [0]*15, "out_pc": CODE+4, "out_nzcv": [0,0,0,0],
            "out_sregs": outs, "out_fpscr": 0}

def encmisc(A, opc2, size, Q, vd=0, vm=2, D=0, M=0):
    return (0xf<<28)|(0b0011<<24)|(1<<23)|(D<<22)|(0b11<<20)|(size<<18)|(A<<16)|(vd<<12)|(opc2<<7)|(Q<<6)|(M<<5)|vm

def encsh(U, imm6, opc, L, Q, vd=0, vm=2, D=0, M=0):
    return (0xf<<28)|(0b001<<25)|(U<<24)|(1<<23)|(D<<22)|(imm6<<16)|(vd<<12)|(opc<<8)|(L<<7)|(Q<<6)|(M<<5)|(1<<4)|vm

def pack_lanes(elem_bits, elems):
    """Pack a list of unsigned element values into a 64-bit D-register value."""
    out = 0
    mask = (1 << elem_bits) - 1
    for i, e in enumerate(elems):
        out |= (int(e) & mask) << (i * elem_bits)
    return out

def d_to_sregs(d_lo, d_hi, s_lo=4, s_hi=6):
    """Set S registers from two D-register values (each is 64-bit)."""
    s = [0]*32
    s[s_lo]   = d_lo & 0xffffffff
    s[s_lo+1] = (d_lo >> 32) & 0xffffffff
    s[s_hi]   = d_hi & 0xffffffff
    s[s_hi+1] = (d_hi >> 32) & 0xffffffff
    return s

# Element value sets for each esize pair (esize_in, esize_out)
# For VQMOVN.s16 (s16→s8): input is s16, output is s8
def s16_vals():
    """s16 values covering in-range, boundary, and overflow."""
    return [0, 1, -1, 0x7F, -0x80, 0x80, -0x81,
            0x7FFF, -0x8000, 0x100, -0x100, 0x200, -0x200,
            0x7F00, -0x7F00, random.randint(-32768, 32767),
            random.randint(-32768, 32767)]

def u16_vals():
    """u16 values for VQMOVN.u16→u8: include above-255 cases."""
    return [0, 1, 0xFF, 0x100, 0x101, 0x180, 0x1FF, 0x200,
            0x7FFF, 0x8000, 0x8001, 0xFFFF, 0xFFFE,
            random.randint(0, 65535), random.randint(256, 65535)]

def s32_vals():
    """s32 values covering s16→s16 boundary."""
    return [0, 1, -1, 0x7FFF, -0x8000, 0x8000, -0x8001,
            0x7FFFFFFF, -0x80000000, 0x10000, -0x10000,
            random.randint(-2**31, 2**31-1), random.randint(-2**31, 2**31-1)]

def u32_vals():
    """u32 values for VQMOVN.u32→u16."""
    return [0, 1, 0xFFFF, 0x10000, 0x10001, 0x20000,
            0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE,
            random.randint(0, 2**32-1), random.randint(65536, 2**32-1)]

vecs = []

# --- 2-reg-misc: VQMOVN.s (op=0, signed→signed) ---
# sz=0: s16→s8 (8 lanes in D), sz=1: s32→s16 (4 lanes), sz=2: s64→s32 (2 lanes)
for sz, esize_out, val_fn in [(0, 8, s16_vals), (1, 16, s32_vals)]:
    esize_in = esize_out * 2
    n_out = 64 // esize_out      # output lanes per D register
    n_in = 128 // esize_in       # input lanes per Q register
    w = encmisc(2, 5, sz, 0)    # VQMOVN.s: A=2, opc2=5, Q=0
    vals = val_fn()
    # Build input Q1 = D2:D3 from val_fn; output → D0
    for batch_start in range(0, max(len(vals), n_in*2), n_in):
        batch = [vals[(batch_start + i) % len(vals)] for i in range(n_in)]
        # Convert to unsigned for packing (handle negatives)
        mask_in = (1 << esize_in) - 1
        ubatch = [v & mask_in for v in batch]
        d2 = pack_lanes(esize_in, ubatch[:n_in//2])
        d3 = pack_lanes(esize_in, ubatch[n_in//2:])
        v = emit(w, d_to_sregs(d2, d3))
        if v:
            vecs.append(v)

# --- 2-reg-misc: VQMOVUN (op=1, signed→unsigned) ---
for sz, esize_out, val_fn in [(0, 8, s16_vals), (1, 16, s32_vals)]:
    esize_in = esize_out * 2
    n_in = 128 // esize_in
    w = encmisc(2, 4, sz, 1)   # VQMOVUN: A=2, opc2=4, Q=1
    vals = val_fn()
    for batch_start in range(0, max(len(vals), n_in*2), n_in):
        batch = [vals[(batch_start + i) % len(vals)] for i in range(n_in)]
        mask_in = (1 << esize_in) - 1
        ubatch = [v & mask_in for v in batch]
        d2 = pack_lanes(esize_in, ubatch[:n_in//2])
        d3 = pack_lanes(esize_in, ubatch[n_in//2:])
        v = emit(w, d_to_sregs(d2, d3))
        if v:
            vecs.append(v)

# --- 2-reg-misc: VQMOVN.u (op=2, unsigned→unsigned) ---
for sz, esize_out, val_fn in [(0, 8, u16_vals), (1, 16, u32_vals)]:
    esize_in = esize_out * 2
    n_in = 128 // esize_in
    w = encmisc(2, 5, sz, 1)   # VQMOVN.u: A=2, opc2=5, Q=1
    vals = val_fn()
    for batch_start in range(0, max(len(vals), n_in*2), n_in):
        batch = [vals[(batch_start + i) % len(vals)] for i in range(n_in)]
        mask_in = (1 << esize_in) - 1
        ubatch = [v & mask_in for v in batch]
        d2 = pack_lanes(esize_in, ubatch[:n_in//2])
        d3 = pack_lanes(esize_in, ubatch[n_in//2:])
        v = emit(w, d_to_sregs(d2, d3))
        if v:
            vecs.append(v)

# --- Shift-narrow: VQSHRN.s (U=0, opc=1001, signed→signed) ---
# esize=8 from s16 (imm6=0x08-0x0F=sh:1-8), esize=16 from s32 (imm6=0x10-0x1F)
def add_shift_narrow(U, opc, esize_out, imm6_base, n_shifts, val_fn):
    esize_in = esize_out * 2
    n_in = 128 // esize_in
    mask_in = (1 << esize_in) - 1
    vals = val_fn()
    for sh_idx in range(n_shifts):
        imm6 = imm6_base + sh_idx
        w = encsh(U, imm6, opc, 0, 0)
        for batch_start in range(0, max(len(vals), n_in*2), n_in):
            batch = [vals[(batch_start + i) % len(vals)] for i in range(n_in)]
            ubatch = [v & mask_in for v in batch]
            d2 = pack_lanes(esize_in, ubatch[:n_in//2])
            d3 = pack_lanes(esize_in, ubatch[n_in//2:])
            v = emit(w, d_to_sregs(d2, d3))
            if v:
                vecs.append(v)

# VQSHRN.s: U=0, opc=0b1001; esize_out=8 from s16 (sh=1..8), esize_out=16 from s32 (sh=1..16)
add_shift_narrow(0, 0b1001, 8,  0x08, 8,  s16_vals)
add_shift_narrow(0, 0b1001, 16, 0x10, 8,  s32_vals)

# VQSHRUN: U=1, opc=0b1000; signed input → unsigned output
add_shift_narrow(1, 0b1000, 8,  0x08, 8,  s16_vals)
add_shift_narrow(1, 0b1000, 16, 0x10, 8,  s32_vals)

# VQSHRN.u: U=1, opc=0b1001; unsigned input → unsigned output
add_shift_narrow(1, 0b1001, 8,  0x08, 8,  u16_vals)
add_shift_narrow(1, 0b1001, 16, 0x10, 8,  u32_vals)

# VSHRN: U=0, opc=0b1000 (reference, should still pass)
add_shift_narrow(0, 0b1000, 8,  0x08, 4,  u16_vals)
add_shift_narrow(0, 0b1000, 16, 0x10, 4,  u32_vals)

outfile = sys.argv[1] if len(sys.argv) > 1 else '/tmp/a32-narrow-sat-vectors.json'
json.dump({"arch": "a32", "group": "narrow-sat", "oracle": "unicorn",
           "vectors": vecs}, open(outfile, 'w'))
print(f"Generated {len(vecs)} vectors -> {outfile}", file=sys.stderr)
