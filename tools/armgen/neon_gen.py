#!/usr/bin/env python3
# OFFLINE oracle for Advanced SIMD (NEON): run each encoding with random Q0-Q7
# (=D0-D15=S0-S31) inputs and capture outputs. The pure-Lean arm_vec_check
# validates via its S-register compare (which covers Q0-Q7). Not in the build.
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *
random.seed(41)
CODE=0x10000; DATA=0x20000
REGS=[UC_ARM_REG_R0+i for i in range(13)]+[UC_ARM_REG_SP,UC_ARM_REG_LR]
SREGN=[UC_ARM_REG_S0+i for i in range(32)]
def run(word, sregs):
    mu=Uc(UC_ARCH_ARM,UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE,0x1000); mu.mem_map(DATA,0x1000)
    mu.reg_write(UC_ARM_REG_C1_C0_2,0x00f00000); mu.reg_write(UC_ARM_REG_FPEXC,0x40000000); mu.reg_write(UC_ARM_REG_FPSCR,0)
    mu.mem_write(CODE,struct.pack('<I',word))
    for i in range(32): mu.reg_write(SREGN[i], sregs[i]&0xffffffff)
    mu.reg_write(UC_ARM_REG_CPSR,0x13)
    try: mu.emu_start(CODE,CODE+4,count=1)
    except UcError: return None
    return [mu.reg_read(SREGN[i])&0xffffffff for i in range(32)]

WIN_LO=0x20020; WIN_HI=0x20060
def run_mem(word, rn_val, premem, store_sregs=None):
    mu=Uc(UC_ARCH_ARM,UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN); mu.mem_map(CODE,0x1000); mu.mem_map(DATA,0x1000)
    mu.reg_write(UC_ARM_REG_C1_C0_2,0x00f00000); mu.reg_write(UC_ARM_REG_FPEXC,0x40000000); mu.reg_write(UC_ARM_REG_FPSCR,0)
    mu.mem_write(CODE,struct.pack("<I",word)); mu.mem_write(WIN_LO,bytes(premem))
    mu.reg_write(UC_ARM_REG_R1, rn_val); mu.reg_write(UC_ARM_REG_R3, 16)  # r3 used as reg offset
    sr=store_sregs or [random.getrandbits(32) for _ in range(32)]
    for i in range(32): mu.reg_write(UC_ARM_REG_S0+i, sr[i]&0xffffffff)
    mu.reg_write(UC_ARM_REG_CPSR,0x13)
    try: mu.emu_start(CODE,CODE+4,count=1)
    except UcError: return None
    outs=[mu.reg_read(UC_ARM_REG_S0+i)&0xffffffff for i in range(32)]
    postmem=list(mu.mem_read(WIN_LO,WIN_HI-WIN_LO))
    regs=[mu.reg_read(UC_ARM_REG_R0+i)&0xffffffff for i in range(13)]+[mu.reg_read(UC_ARM_REG_SP)&0xffffffff,mu.reg_read(UC_ARM_REG_LR)&0xffffffff]
    return outs, postmem, regs, sr
def emit_mem(word):
    pre=[((0x13+i*7)&0xff) for i in range(WIN_HI-WIN_LO)]
    r=run_mem(word, WIN_LO+0x10, pre)
    if r is None: return
    outs,postmem,regs,sr=r
    inregs=[0]*15; inregs[1]=WIN_LO+0x10; inregs[3]=16
    vecs.append({"insn":word,"in_regs":inregs,"in_nzcv":[0,0,0,0],"in_sregs":sr,
                 "out_regs":regs,"out_pc":CODE+4,"out_nzcv":[0,0,0,0],"out_sregs":outs,"out_fpscr":0,
                 "mem_base":WIN_LO,"pre_mem":pre,"post_mem":postmem})

vecs=[]
def emit(word):
    sregs=[random.getrandbits(32) for _ in range(32)]
    outs=run(word, sregs)
    if outs is None: return
    vecs.append({"insn":word,"in_regs":[0]*15,"in_nzcv":[0,0,0,0],"in_sregs":sregs,
                 "out_regs":[0]*15,"out_pc":CODE+4,"out_nzcv":[0,0,0,0],"out_sregs":outs,"out_fpscr":0})

def enc3(U,sz,Q,opc,vd,vn,vm,o4=1,D=0,N=0,M=0):  # 3-reg-same: 1111 001 U 0 D sz Vn Vd opc N Q M o4 Vm
    return (0xf<<28)|(0b001<<25)|(U<<24)|(D<<22)|(sz<<20)|(vn<<16)|(vd<<12)|(opc<<8)|(N<<7)|(Q<<6)|(M<<5)|(o4<<4)|vm

# P1 bitwise: opc=0001, o4=1; (U,sz) selects the op. D-form (D0,D1,D2) + Q-form (Q0,Q1,Q2).
for (U,sz) in [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)]:
    for _ in range(25): emit(enc3(U,sz,0,0b0001,0,1,2))      # Dd=0,Dn=1,Dm=2
    for _ in range(25): emit(enc3(U,sz,1,0b0001,0,2,4))      # Qd=0,Qn=1,Qm=2 (D0,D2,D4)

# P3 integer arithmetic
for sz in (0,1,2,3):              # VADD/VSUB .I8/16/32/64
    for _ in range(15): emit(enc3(0,sz,0,0b1000,0,1,2,o4=0))   # VADD D
    for _ in range(15): emit(enc3(1,sz,0,0b1000,0,1,2,o4=0))   # VSUB D
    for _ in range(15): emit(enc3(0,sz,1,0b1000,0,2,4,o4=0))   # VADD Q
    for _ in range(15): emit(enc3(1,sz,1,0b1000,0,2,4,o4=0))   # VSUB Q
for sz in (0,1,2):               # VMUL/VMLA/VMLS .I8/16/32
    for _ in range(15): emit(enc3(0,sz,0,0b1001,0,1,2,o4=1))   # VMUL D
    for _ in range(15): emit(enc3(0,sz,1,0b1001,0,2,4,o4=1))   # VMUL Q
    for _ in range(15): emit(enc3(0,sz,0,0b1001,0,1,2,o4=0))   # VMLA D
    for _ in range(15): emit(enc3(1,sz,0,0b1001,0,1,2,o4=0))   # VMLS D
    for _ in range(15): emit(enc3(0,sz,1,0b1001,0,2,4,o4=0))   # VMLA Q


# P4 compare / min-max / abs-diff / halving (U=0 signed, U=1 unsigned)
for U in (0,1):
    for sz in (0,1,2):
        for _ in range(10): emit(enc3(U,sz,0,0b0011,0,1,2,o4=0))   # VCGT
        for _ in range(10): emit(enc3(U,sz,0,0b0011,0,1,2,o4=1))   # VCGE
        for _ in range(10): emit(enc3(U,sz,0,0b0110,0,1,2,o4=0))   # VMAX
        for _ in range(10): emit(enc3(U,sz,0,0b0110,0,1,2,o4=1))   # VMIN
        for _ in range(10): emit(enc3(U,sz,0,0b0111,0,1,2,o4=0))   # VABD
        for _ in range(10): emit(enc3(U,sz,0,0b0000,0,1,2,o4=0))   # VHADD
        for _ in range(10): emit(enc3(U,sz,0,0b0001,0,1,2,o4=0))   # VRHADD
        for _ in range(10): emit(enc3(U,sz,0,0b0010,0,1,2,o4=0))   # VHSUB
        for _ in range(10): emit(enc3(U,sz,1,0b0110,0,2,4,o4=0))   # VMAX Q
for sz in (0,1,2):
    for _ in range(12): emit(enc3(1,sz,0,0b1000,0,1,2,o4=1))       # VCEQ
    for _ in range(12): emit(enc3(0,sz,0,0b1000,0,1,2,o4=1))       # VTST


# P2 modified immediate VMOV.i / VMVN.i
def enc1imm(i,D,imm3,vd,cmode,Q,op,imm4):
    return (0xf<<28)|(0b001<<25)|(i<<24)|(1<<23)|(D<<22)|(imm3<<16)|(vd<<12)|(cmode<<8)|(Q<<6)|(op<<5)|(1<<4)|imm4
import random as _r
for cmode in range(16):
    for op in (0,1):
        # skip VORR/VBIC (cmode<0>=1 and cmode<3:1> < 6) and undefined cmode 1111 op1
        if (cmode&1)==1 and (cmode>>1)<6: continue
        if cmode==0b1111 and op==1: continue
        for _ in range(8):
            v=_r.getrandbits(8)
            emit(enc1imm((v>>7)&1,0,(v>>4)&7,0,cmode,0,op,v&0xf))   # D
            emit(enc1imm((v>>7)&1,0,(v>>4)&7,0,cmode,1,op,v&0xf))   # Q


# P5 shifts
def encsh(U,imm6,opc,L,Q,vd=0,vm=2,D=0,M=0):
    return (0xf<<28)|(0b001<<25)|(U<<24)|(1<<23)|(D<<22)|(imm6<<16)|(vd<<12)|(opc<<8)|(L<<7)|(Q<<6)|(M<<5)|(1<<4)|vm
# register shifts VSHL/VRSHL (3-reg-same opc 0100/0101 o4=0): value=Dm(2), shift=Dn(1)
for U in (0,1):
    for sz in (0,1,2,3):
        for opc in (0b0100,0b0101):
            if sz==3 and opc==0b0100: continue   # VSHL.64 reg crashes Unicorn's JIT (oracle bug)
            for _ in range(12): emit(enc3(U,sz,0,opc,0,1,2,o4=0))   # D
            for _ in range(12): emit(enc3(U,sz,1,opc,0,2,4,o4=0))   # Q
# immediate shifts: esize via imm6 high bit; right opc 0000-0011/0100, left 0101
ESBASE={8:0b001000,16:0b010000,32:0b100000}
for U in (0,1):
    for opc in (0b0000,0b0001,0b0010,0b0011,0b0100,0b0101):
        for es,base in ESBASE.items():
            for sh in range(es):       # imm6 = base+sh covers shift range
                imm6=base+sh
                emit(encsh(U,imm6,opc,0,0))            # D
                emit(encsh(U,imm6,opc,0,1,vd=0,vm=4))  # Q
        # esize=64 uses L=1, imm6 full
        for sh in range(0,64,7):
            emit(encsh(U,sh&0x3f,opc,1,0))


# P6 saturating
for U in (0,1):
    for sz in (0,1,2,3):
        for opc in (0b0000,0b0010):            # VQADD/VQSUB (3-reg o4=1)
            if sz==3: continue                 # VQADD/VQSUB.64 D-form crashes Unicorn's JIT
            for _ in range(12): emit(enc3(U,sz,0,opc,0,1,2,o4=1))
            for _ in range(12): emit(enc3(U,sz,1,opc,0,2,4,o4=1))
        for opc in (0b0100,0b0101):            # VQSHL/VQRSHL reg (o4=1)
            if sz==3 and opc==0b0100: continue # VQSHL.64 reg crashes Unicorn's JIT
            for _ in range(12): emit(enc3(U,sz,0,opc,0,1,2,o4=1))
            for _ in range(12): emit(enc3(U,sz,1,opc,0,2,4,o4=1))
# VQSHL/VQSHLU immediate (opc 0111 VQSHL U=s; opc 0110 U=1 VQSHLU)
for es,base in {8:0b001000,16:0b010000,32:0b100000}.items():
    for sh in range(es):
        for U in (0,1):
            emit(encsh(U,base+sh,0b0111,0,0)); emit(encsh(U,base+sh,0b0111,0,1,vd=0,vm=4))  # VQSHL
        emit(encsh(1,base+sh,0b0110,0,0)); emit(encsh(1,base+sh,0b0110,0,1,vd=0,vm=4))        # VQSHLU
for sh in range(0,64,5):
    for U in (0,1): emit(encsh(U,sh&0x3f,0b0111,1,0))
    emit(encsh(1,sh&0x3f,0b0110,1,0))


# P8 two-register misc: VREV/VCLS/VCLZ/VCNT/VMVN, VABS/VNEG int, VSWP/VTRN/VUZP/VZIP
def encmisc(A,opc2,size,Q,vd=0,vm=2,D=0,M=0):
    return (0xf<<28)|(0b0011<<24)|(1<<23)|(D<<22)|(0b11<<20)|(size<<18)|(A<<16)|(vd<<12)|(opc2<<7)|(Q<<6)|(M<<5)|vm
for Q,vd,vm in [(0,0,2),(1,0,4)]:
    for size in (0,1,2):
        for opc2 in (8,9,0xa,0xb):  # VCLS/VCLZ/VCNT/VMVN (A=0)
            if opc2==0xa and size!=0: continue   # VCNT only .8
            if opc2==0xb and size!=0: continue   # VMVN (misc) size ignored; emit once
            emit(encmisc(0,opc2,size,Q,vd,vm))
        for opc2 in (6,7):          # VABS/VNEG int (A=1)
            emit(encmisc(1,opc2,size,Q,vd,vm))
        for opc2 in (0,1,2,3):      # VSWP/VTRN/VUZP/VZIP (A=2)
            emit(encmisc(2,opc2,size,Q,vd,vm))
    # VREV: opc2 0/1/2 region 64/32/16; esize<region
    for opc2,maxsize in [(0,3),(1,2),(2,1)]:  # rev64 allows size 0-2, rev32 0-1, rev16 0
        for size in range(maxsize):
            emit(encmisc(0,opc2,size,Q,vd,vm))


# VDUP scalar + VEXT
def encdupsc(imm4,Q,vd=0,vm=2,D=0,M=0):
    return (0xf<<28)|(0b0011<<24)|(1<<23)|(D<<22)|(0b11<<20)|(imm4<<16)|(vd<<12)|(0b11000<<7)|(Q<<6)|(M<<5)|vm
def encext(imm4,Q,vd=0,vn=1,vm=2,D=0,N=0,M=0):
    return (0xf<<28)|(0b0010<<24)|(1<<23)|(D<<22)|(0b11<<20)|(vn<<16)|(vd<<12)|(imm4<<8)|(N<<7)|(Q<<6)|(M<<5)|vm
for Q,vd,vm in [(0,0,2),(1,0,4)]:
    for imm4 in (0b0001,0b0011,0b0010,0b0110,0b0100,0b1000):  # esize 8/8/16/16/32/32 index
        emit(encdupsc(imm4,Q,vd,vm))
for Q,vd,vn,vm in [(0,0,1,2),(1,0,2,4)]:
    for imm in range(8 if Q==0 else 16):
        emit(encext(imm,Q,vd,vn,vm))


# P9 vector floating-point (3-reg)
fpops=[(0,0,0b1101,0),(0,2,0b1101,0),(0,0,0b1101,1),(0,2,0b1101,1),(1,0,0b1101,1),  # ADD/SUB/MLA/MLS/MUL
       (1,2,0b1101,0),(0,0,0b1100,1),(0,2,0b1100,1),                                 # ABD/FMA/FMS
       (0,0,0b1110,0),(1,0,0b1110,0),(1,2,0b1110,0),(1,0,0b1110,1),(1,2,0b1110,1),    # CEQ/CGE/CGT/ACGE/ACGT
       (0,0,0b1111,0),(0,2,0b1111,0)]   # MAX/MIN (VRECPS/VRSQRTS: QEMU 1-ULP off silicon → native-full oracle)
for (U,sz,opc,o4) in fpops:
    for _ in range(40): emit(enc3(U,sz,0,opc,0,1,2,o4))   # D
    for _ in range(40): emit(enc3(U,sz,1,opc,0,2,4,o4))   # Q
# VABS.f32/VNEG.f32 (2-reg-misc A=01 opc2 0b1110/0b1111, F=bit10=1)
for Q,vd,vm in [(0,0,2),(1,0,4)]:
    emit(encmisc(1,0b1110,2,Q,vd,vm)); emit(encmisc(1,0b1111,2,Q,vd,vm))


# pairwise (D only): VPMAX/VPMIN/VPADD int + VPADD/VPMAX/VPMIN.F32
for U in (0,1):
    for sz in (0,1,2):
        for opc,o4 in [(0b1010,0),(0b1010,1),(0b1011,1)]:
            for _ in range(12): emit(enc3(U,sz,0,opc,0,1,2,o4))
for (U,sz,opc,o4) in [(1,0,0b1101,0),(1,0,0b1111,0),(1,2,0b1111,0)]:  # VPADD/VPMAX/VPMIN.F32
    for _ in range(30): emit(enc3(U,sz,0,opc,0,1,2,o4))


# P7 widening (3-reg-diff)
def encd(U,size,opc,vd=0,vn=2,vm=4,D=0,N=0,M=0):
    return (0xf<<28)|(0b001<<25)|(U<<24)|(1<<23)|(D<<22)|(size<<20)|(vn<<16)|(vd<<12)|(opc<<8)|(N<<7)|(M<<5)|vm
for U in (0,1):
    for size in (0,1,2):
        for opc in (0b0000,0b0010,0b1100,0b0111,0b0001,0b0011,0b1000,0b1010,0b0101):
            for _ in range(12): emit(encd(U,size,opc))


# narrowing/widening: VADDHN/VSUBHN, VMOVN, VMOVL/VSHLL
for U in (0,1):
    for size in (0,1,2):
        for opc in (0b0100,0b0110):   # VADDHN/VSUBHN (+ rounding U=1)
            for _ in range(12): emit(encd(U,size,opc))
for size in (0,1,2):  # VMOVN (A=2 opc2=4)
    emit(encmisc(2,4,size,0,0,2))
for U in (0,1):       # VMOVL/VSHLL (opc 1010); imm6 covers shift incl 0 (VMOVL)
    for es,base in {8:0b001000,16:0b010000,32:0b100000}.items():
        for sh in range(es):
            emit(encsh(U,base+sh,0b1010,0,0,vd=0,vm=2))


# P10 VLD1/VST1 (contiguous, 1-4 regs) with addressing modes
def lsm(L,Rn,Vd,typ,size,align,Rm,D=0): return (0xf<<28)|(0b0100<<24)|(D<<22)|(L<<21)|(Rn<<16)|(Vd<<12)|(typ<<8)|(size<<6)|(align<<4)|Rm
for L in (0,1):
    for typ in (0b0111,0b1010,0b0110,0b0010):  # 1-4 regs
        for size in (0,1,2,3):
            for Rm in (0b1111,0b1101,3):        # none / post-inc / reg(r3)
                emit_mem(lsm(L,1,0,typ,size,0,Rm))


# VLD2/3/4 + VST2/3/4 (de-interleaving)
for L in (0,1):
    for typ in (0b1000,0b0100,0b0000):   # VLD2/VLD3/VLD4
        for size in (0,1,2):
            for Rm in (0b1111,0b1101,3):
                emit_mem(lsm(L,1,0,typ,size,0,Rm))


# VQDMULH/VQRDMULH, VCVT-vector, compare-with-zero
for U in (0,1):
    for sz in (1,2):
        for _ in range(15): emit(enc3(U,sz,0,0b1011,0,1,2,o4=0))   # VQDMULH/VQRDMULH
        for _ in range(15): emit(enc3(U,sz,1,0b1011,0,2,4,o4=0))
for opc2 in (0b1100,0b1101,0b1110,0b1111):   # VCVT (A=3, sz=2 → f32)
    for Q,vd,vm in [(0,0,2),(1,0,4)]: 
        for _ in range(20): emit(encmisc(3,opc2,2,Q,vd,vm))
for op in range(5):   # compare-zero int (A=1, F=0)
    for sz in (0,1,2):
        for Q,vd,vm in [(0,0,2),(1,0,4)]: emit(encmisc(1,op,sz,Q,vd,vm))
    for Q,vd,vm in [(0,0,2),(1,0,4)]: emit(encmisc(1,0b1000|op,2,Q,vd,vm))  # FP compare-zero (F=1)


# VTBL/VTBX (1111 0011 1 D 11 Vn Vd 10 len op N Q M 0 Vm)
def enctbl(len,op,vd=0,vn=1,vm=4,D=0,N=0,M=0):
    return (0xf<<28)|(0b0011<<24)|(1<<23)|(D<<22)|(0b11<<20)|(vn<<16)|(vd<<12)|(0b10<<10)|(len<<8)|(op<<6)|(N<<7)|(M<<5)|vm
for length in range(4):
    for op in (0,1):
        for _ in range(15): emit(enctbl(length,op))


# VPADDL/VPADAL/VQABS/VQNEG (2-reg-misc A=0)
for opc2 in (4,5,12,13,14,15):
    for size in (0,1,2):
        for Q,vd,vm in [(0,0,2),(1,0,4)]: emit(encmisc(0,opc2,size,Q,vd,vm))

print(f"generated {len(vecs)} NEON vectors", file=sys.stderr)
json.dump({"arch":"a32","group":"neon","oracle":"unicorn-2.1.4","vectors":vecs}, open(sys.argv[1] if len(sys.argv)>1 else '/tmp/neon.json','w'))

def enc_narrow():
    """VSHRN/VRSHRN, VQSHRN/VQSHRUN, VQMOVN/VQMOVUN, VQDMULL/VQDMLAL/VQDMLSL."""
    vecs = []
    def add(w, n=10):
        for _ in range(n):
            v = run(w, {})
            if v: vecs.append(v)
    # 2-reg-shift narrowing: VSHRN.8/16/32 (opc=1000 U=0), VRSHRN (U=1)
    for (imm,_) in [(0x01,8),(0x0f,8),(0x11,16),(0x1f,16),(0x21,32),(0x3f,32)]:
        for U in [0,1]:
            w=(0xF<<28)|(1<<25)|(U<<24)|(1<<23)|(imm<<16)|(0<<12)|(0b1000<<8)|(0<<7)|(0<<6)|(0<<5)|(1<<4)|1
            add(w)
    # VQSHRN.s (U=0), VQSHRUN (U=1)
    for imm in [0x08,0x10,0x20]:
        for U in [0,1]:
            w=(0xF<<28)|(1<<25)|(U<<24)|(1<<23)|(imm<<16)|(0<<12)|(0b1001<<8)|(0<<7)|(0<<6)|(0<<5)|(1<<4)|1
            add(w)
    # 2-reg-misc: VQMOVN.s (opc2=5 U=0), VQMOVUN (opc2=5 U=1), VQMOVN.u (U=1 opc2 bit4=1)
    for sz in [0,1,2]:
        for (U,opc2) in [(0,0b0101000),(1,0b0101000),(1,0b0100000)]:
            w=(0xF<<28)|(1<<25)|(U<<24)|(1<<23)|(1<<21)|(sz<<18)|(0b10<<16)|(0<<12)|(opc2<<7)|(0<<4)|1
            add(w)
    # 3-reg-diff: VQDMULL/VQDMLAL/VQDMLSL .s16/.s32
    for sz in [1,2]:
        for opc in [0b1101, 0b1001, 0b1011]:
            w=(0xF<<28)|(1<<25)|(0<<24)|(1<<23)|(sz<<20)|(1<<16)|(0<<12)|(opc<<8)|2
            add(w)
    return vecs

if __name__ == '__main__' and 'narrow' in __import__('sys').argv[-1]:
    all_vecs.extend(enc_narrow())
