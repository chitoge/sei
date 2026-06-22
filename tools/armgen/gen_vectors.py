#!/usr/bin/env python3
# OFFLINE ORACLE (dev tool, NOT part of the SEI Lean build): generate A32
# golden-vector test data by single-stepping instructions in Unicorn, so the
# Lean A32 executor can be validated against a trusted reference. Output is a
# committed JSON corpus; the Lean test reads it with zero Python dependency.
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *

CODE = 0x10000          # instruction lives here
REGS = [UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3,UC_ARM_REG_R4,
        UC_ARM_REG_R5,UC_ARM_REG_R6,UC_ARM_REG_R7,UC_ARM_REG_R8,UC_ARM_REG_R9,
        UC_ARM_REG_R10,UC_ARM_REG_R11,UC_ARM_REG_R12,UC_ARM_REG_R13,UC_ARM_REG_R14]

def cpsr_nzcv(c): return ((c>>31)&1, (c>>30)&1, (c>>29)&1, (c>>28)&1)

def run_one(word, regs, nzcv):
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM | UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE, 0x1000)
    mu.mem_write(CODE, struct.pack('<I', word))
    for i,r in enumerate(REGS): mu.reg_write(r, regs[i] & 0xffffffff)
    n,z,cf,v = nzcv
    cpsr = (n<<31)|(z<<30)|(cf<<29)|(v<<28)|0x13   # SVC mode, ARM state
    mu.reg_write(UC_ARM_REG_CPSR, cpsr)
    try:
        mu.emu_start(CODE, CODE+4, count=1)
    except UcError:
        return None
    out = [mu.reg_read(r) & 0xffffffff for r in REGS]
    pc = mu.reg_read(UC_ARM_REG_PC) & 0xffffffff
    return out, pc, cpsr_nzcv(mu.reg_read(UC_ARM_REG_CPSR))

def vec(word, regs, nzcv):
    regs = [x & 0xffffffff for x in regs]   # snapshot (caller mutates its list later)
    r = run_one(word, regs, nzcv)
    if r is None: return None
    out, pc, onzcv = r
    return {"insn": word, "in_regs": regs, "in_nzcv": list(nzcv),
            "out_regs": out, "out_pc": pc, "out_nzcv": list(onzcv)}

random.seed(0xA32)
def rr(): return random.getrandbits(32)
def randregs(): return [rr() for _ in range(15)]

# DP register-shifted and immediate forms across opcodes + shift types + S bit.
# Encodings built generically: cond=AL(0xe).
def dp_imm(op, s, rn, rd, rot, imm8):
    return (0xe<<28)|(1<<25)|(op<<21)|(s<<20)|(rn<<16)|(rd<<12)|(rot<<8)|imm8
def dp_reg_immshift(op, s, rn, rd, sh_imm, sh_type, rm):
    return (0xe<<28)|(op<<21)|(s<<20)|(rn<<16)|(rd<<12)|(sh_imm<<7)|(sh_type<<5)|rm
def dp_reg_regshift(op, s, rn, rd, rs, sh_type, rm):
    return (0xe<<28)|(op<<21)|(s<<20)|(rn<<16)|(rd<<12)|(rs<<8)|(sh_type<<5)|(1<<4)|rm

vectors = []
edge_regvals = [0,1,2,0x7fffffff,0x80000000,0xffffffff,0xfffffffe,0x100,0xdeadbeef,0x12345678]
for op in range(16):              # AND..MVN incl TST/TEQ/CMP/CMN
    for s in (0,1):
        # opcodes 8-B (TST/TEQ/CMP/CMN) with S=0 are NOT data-processing — that
        # encoding is the MRS/MSR/misc space. Only emit the valid (S=1) form.
        if op in (0x8,0x9,0xA,0xB) and s == 0: continue
        for trial in range(6):
            regs = randregs()
            # seed some edge values
            regs[1] = random.choice(edge_regvals); regs[2] = random.choice(edge_regvals)
            nzcv = (random.getrandbits(1),)*1 + tuple(random.getrandbits(1) for _ in range(3))
            nzcv = tuple(random.getrandbits(1) for _ in range(4))
            # immediate form
            v = vec(dp_imm(op,s,1,0,random.randint(0,15),random.randint(0,255)), regs, nzcv)
            if v: vectors.append(v)
            # register, immediate shift (all shift types)
            for st in range(4):
                v = vec(dp_reg_immshift(op,s,1,0,random.randint(0,31),st,2), regs, nzcv)
                if v: vectors.append(v)
            # register, register shift
            regs[3] = random.randint(0,40)
            v = vec(dp_reg_regshift(op,s,1,0,3,random.randint(0,3),2), regs, nzcv)
            if v: vectors.append(v)

# Conditional execution: test condHolds for DP ops (branches test it too, but DP is orthogonal)
for cond, nzcv_taken, nzcv_not in [
    (0x0, (0,1,0,0), (0,0,0,0)),   # EQ: taken=Z=1, not=Z=0
    (0x1, (0,0,0,0), (0,1,0,0)),   # NE: taken=Z=0, not=Z=1
    (0x2, (0,0,1,0), (0,0,0,0)),   # CS/HS: taken=C=1, not=C=0
    (0x8, (1,0,0,0), (0,0,0,0)),   # HI: taken=C=1,Z=0 (approx), not=N=1,Z=0
    (0xB, (1,0,0,1), (0,0,0,0)),   # LT: N≠V → taken=N=1,V=0; not=same flags → not taken
]:
    regs_c = [0]*15; regs_c[1] = 0xDEADBEEF; regs_c[2] = 0xCAFEBABE
    v = vec((cond<<28)|(1<<25)|(0x4<<21)|(0<<20)|(1<<16)|(2<<12)|5, regs_c, nzcv_taken)
    if v: vectors.append(v)   # ADD r2, r1, #5 (taken)
    v = vec((cond<<28)|(1<<25)|(0x4<<21)|(0<<20)|(1<<16)|(2<<12)|5, regs_c, nzcv_not)
    if v: vectors.append(v)   # ADD r2, r1, #5 (not taken → r2 unchanged)

# Extra pass: varied Rd to expose any Rd field decode bug (ops that write Rd)
for op in [0x0, 0x1, 0x2, 0x4, 0xC, 0xD, 0xE, 0xF]:   # AND/EOR/SUB/ADD/ORR/MOV/BIC/MVN
    for rd in [2, 4, 7, 11]:
        regs = randregs(); regs[1] = random.choice(edge_regvals); regs[2] = random.choice(edge_regvals)
        nzcv = tuple(random.getrandbits(1) for _ in range(4))
        v = vec(dp_imm(op,0,1,rd,0,0xAA), regs, nzcv)
        if v: vectors.append(v)
        v = vec(dp_reg_immshift(op,0,1,rd,4,0,2), regs, nzcv)
        if v: vectors.append(v)

print(f"generated {len(vectors)} DP vectors", file=sys.stderr)
json.dump({"arch":"a32","group":"dp","oracle":"unicorn-2.1.4","vectors":vectors},
          open(sys.argv[1] if len(sys.argv)>1 else "vectors.json","w"))

# ---- Load/store (word & unsigned byte): imm/reg offset, pre/post, writeback ----
DATA = 0x20000
WIN_LO, WIN_HI = 0x20020, 0x20060          # 64-byte capture window
BASE = 0x20040

def ldst_enc(P,U,B,W,L,rn,rt,off, isreg=False, sh_type=0, sh_imm=0):
    base = (0xe<<28)|(1<<26)|(P<<24)|(U<<23)|(B<<22)|(W<<21)|(L<<20)|(rn<<16)|(rt<<12)
    return base|(1<<25)|(sh_imm<<7)|(sh_type<<5)|(off&0xf) if isreg else base|(off&0xfff)

def run_ldst(word, regs, premem):
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM | UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE, 0x1000); mu.mem_map(DATA, 0x1000)
    mu.mem_write(CODE, struct.pack('<I', word))
    mu.mem_write(WIN_LO, bytes(premem))
    for i,r in enumerate(REGS): mu.reg_write(r, regs[i] & 0xffffffff)
    mu.reg_write(UC_ARM_REG_CPSR, 0x13)
    try: mu.emu_start(CODE, CODE+4, count=1)
    except UcError: return None
    out = [mu.reg_read(r) & 0xffffffff for r in REGS]
    postmem = list(mu.mem_read(WIN_LO, WIN_HI-WIN_LO))
    return out, mu.reg_read(UC_ARM_REG_PC) & 0xffffffff, postmem

ldst_vectors = []
def emit_ldst(word, r1off=0, r2val=4):
    regs = [0]*15
    regs[1] = BASE + r1off                 # rn
    regs[2] = r2val                        # register offset
    regs[0] = 0xCAFEF00D                   # rt source for stores
    premem = [(0x10+i) & 0xff for i in range(WIN_HI-WIN_LO)]
    r = run_ldst(word, regs, premem)
    if r is None: return
    out, pc, postmem = r
    ldst_vectors.append({"insn": word, "in_regs": [x&0xffffffff for x in regs], "in_nzcv":[0,0,0,0],
        "mem_base": WIN_LO, "pre_mem": premem,
        "out_regs": out, "out_pc": pc, "out_nzcv":[0,0,0,0], "post_mem": postmem})

for L in (0,1):                            # load / store
    for B in (0,1):                        # word / byte
        for P in (0,1):                    # post / pre index
            for U in (0,1):                # down / up
                for W in (0,1):
                    if P==0 and W==1: continue          # post-index W=1 is unprivileged (skip)
                    # immediate offset (rn=r1, rt=r0)
                    for imm in (0,4,8,0xc,0x1c):
                        emit_ldst(ldst_enc(P,U,B,W,L,1,0,imm))
                    # register offset (rn=r1, rm=r2), with a couple shift types
                    for st in (0,1):
                        emit_ldst(ldst_enc(P,U,B,W,L,1,0,2,isreg=True,sh_type=st,sh_imm=2))

# Extra: varied Rt (data register) to exercise (w>>>12)&0xf path
def emit_ldst_rt(word, rt, stval=0xDEADBEEF):
    regs = [0]*15
    regs[1] = BASE           # rn
    regs[2] = 4              # rm
    regs[rt] = stval         # rt source for stores
    if rt != 1: regs[1] = BASE  # keep rn = BASE (might have been overwritten above)
    premem = [(0x20+i) & 0xff for i in range(WIN_HI-WIN_LO)]
    r = run_ldst(word, regs, premem)
    if r is None: return
    out, pc, postmem = r
    ldst_vectors.append({"insn": word, "in_regs": [x&0xffffffff for x in regs], "in_nzcv":[0,0,0,0],
        "mem_base": WIN_LO, "pre_mem": premem,
        "out_regs": out, "out_pc": pc, "out_nzcv":[0,0,0,0], "post_mem": postmem})
for rt in [3, 5, 7, 11]:
    for L in (0, 1):
        for B in (0, 1):
            # Pre-indexed, up, no writeback (simplest form): P=1,U=1,W=0
            emit_ldst_rt(ldst_enc(1,1,B,0,L,1,rt,0), rt)
# Large imm12 offsets (exercise full 12-bit range; currently max is 0x1c)
for imm in [0x100, 0x400, 0xFFF, 0x7FF]:
    for (L, B, r1off) in [(1,0,0),(1,1,0),(0,0,0),(0,1,0)]:
        # Pre-indexed up no-wb with large positive offset from BASE-imm to stay in window
        # Use r1off to center address in WIN region
        emit_ldst(ldst_enc(1,1,B,0,L,1,0,imm), r1off=-imm)

print(f"generated {len(ldst_vectors)} LDST vectors", file=sys.stderr)
if len(sys.argv) > 2:
    json.dump({"arch":"a32","group":"ldst","oracle":"unicorn-2.1.4","vectors":ldst_vectors},
              open(sys.argv[2],"w"))

# ---- Multiply (MUL/MLA/UMULL/UMLAL/SMULL/SMLAL) ----
def mul_enc(opc, s, rdhi, rdlo, rs, rm):
    return (0xe<<28)|(opc<<21)|(s<<20)|(rdhi<<16)|(rdlo<<12)|(rs<<8)|(0b1001<<4)|rm
mul_vectors = []
mvals = [0,1,2,0xffffffff,0x7fffffff,0x80000000,0x10000,0xdeadbeef,3,0x12345678,0xffff]
for opc in (0,1,4,5,6,7):
    for s in (0,1):
        for _ in range(10):
            regs=[0]*15
            regs[1]=random.choice(mvals)   # Rm
            regs[2]=random.choice(mvals)   # Rs
            regs[3]=random.choice(mvals)   # Ra / unused
            regs[4]=random.choice(mvals); regs[5]=random.choice(mvals)  # RdHi/RdLo seed (accumulate)
            if opc in (0,1): w=mul_enc(opc,s,0,3,2,1)         # Rd=r0, Ra=r3, Rs=r2, Rm=r1
            else: w=mul_enc(opc,s,4,5,2,1)                    # RdHi=r4, RdLo=r5, Rs=r2, Rm=r1
            v=vec(w, regs, (0,0,0,0))
            if v: mul_vectors.append(v)
print(f"generated {len(mul_vectors)} MUL vectors", file=sys.stderr)
if len(sys.argv) > 3:
    json.dump({"arch":"a32","group":"mul","oracle":"unicorn-2.1.4","vectors":mul_vectors},
              open(sys.argv[3],"w"))

# ---- Extra load/store: LDRH/STRH/LDRSB/LDRSH/LDRD/STRD ----
def xldst_enc(P,U,I,W,L,rn,rt,op2,imm=0,rm=0):
    base=(0xe<<28)|(P<<24)|(U<<23)|(I<<22)|(W<<21)|(L<<20)|(rn<<16)|(rt<<12)|(1<<7)|(op2<<5)|(1<<4)
    return base|((((imm>>4)&0xf)<<8)|(imm&0xf)) if I else base|(rm&0xf)
xldst_vectors=[]
def emit_xldst(word, rt):
    regs=[0]*15; regs[1]=BASE; regs[4]=4; regs[0]=0xBEEFCAFE; regs[3]=0x0BADF00D
    premem=[((0x83+i*7)&0xff) for i in range(WIN_HI-WIN_LO)]   # high bits set ⇒ exercises sign-extend
    r=run_ldst(word, regs, premem)
    if r is None: return
    out,pc,postmem=r
    xldst_vectors.append({"insn":word,"in_regs":[x&0xffffffff for x in regs],"in_nzcv":[0,0,0,0],
        "mem_base":WIN_LO,"pre_mem":premem,"out_regs":out,"out_pc":pc,"out_nzcv":[0,0,0,0],"post_mem":postmem})
for (L,op2,rt) in [(1,1,0),(1,2,0),(1,3,0),(0,1,0),(0,2,2),(0,3,2)]:  # LDRH/LDRSB/LDRSH/STRH/LDRD/STRD
    for P in (0,1):
        for U in (0,1):
            for W in (0,1):
                if P==0 and W==1: continue
                for imm in (0,2,4,8):
                    emit_xldst(xldst_enc(P,U,1,W,L,1,rt,op2,imm=imm), rt)
                emit_xldst(xldst_enc(P,U,0,W,L,1,rt,op2,rm=4), rt)   # register offset
# Extra: varied Rt for LDRH/LDRSB/LDRSH/STRH forms (not LDRD/STRD which need even Rt)
def emit_xldst_rt(word, rt, stval=0xABCDEF12):
    regs=[0]*15; regs[1]=BASE; regs[4]=4
    regs[rt]=stval           # rt source for stores; rn stays BASE since rt != 1
    premem=[((0x83+i*7)&0xff) for i in range(WIN_HI-WIN_LO)]
    r=run_ldst(word, regs, premem)
    if r is None: return
    out,pc,postmem=r
    xldst_vectors.append({"insn":word,"in_regs":[x&0xffffffff for x in regs],"in_nzcv":[0,0,0,0],
        "mem_base":WIN_LO,"pre_mem":premem,"out_regs":out,"out_pc":pc,"out_nzcv":[0,0,0,0],"post_mem":postmem})
for rt in [3, 5, 7]:
    for (L, op2) in [(1,1),(1,2),(1,3),(0,1)]:  # LDRH/LDRSB/LDRSH/STRH
        # Pre-indexed, up, no writeback: P=1,U=1,I=1,W=0 (imm offset=0)
        emit_xldst_rt(xldst_enc(1,1,1,0,L,1,rt,op2,imm=0), rt)

print(f"generated {len(xldst_vectors)} XLDST vectors", file=sys.stderr)
if len(sys.argv) > 4:
    json.dump({"arch":"a32","group":"xldst","oracle":"unicorn-2.1.4","vectors":xldst_vectors},
              open(sys.argv[4],"w"))

# ---- MRS / MSR (status register, CPSR) ----
def mrs_enc(R,rd): return (0xe<<28)|(0b00010<<23)|(R<<22)|(0xf<<16)|(rd<<12)
def msr_reg_enc(R,mask,rm): return (0xe<<28)|(0b00010<<23)|(R<<22)|(2<<20)|(mask<<16)|(0xf<<12)|rm
def msr_imm_enc(R,mask,rot,imm8): return (0xe<<28)|(0b00110<<23)|(R<<22)|(2<<20)|(mask<<16)|(0xf<<12)|(rot<<8)|imm8
msr_vectors=[]
for rd in (0,1,5):                                    # MRS rd, CPSR
    for nzcv in [(0,0,0,0),(1,1,1,1),(1,0,1,0),(0,1,0,1)]:
        v=vec(mrs_enc(0,rd),[0]*15,nzcv)
        if v: msr_vectors.append(v)
for nzcv in [(0,0,0,0),(1,1,1,1)]:                    # MSR CPSR_f, rm
    for fv in [0x00000000,0xf0000000,0x80000000,0x30000000,0xc0000000]:
        regs=[0]*15; regs[1]=fv
        v=vec(msr_reg_enc(0,8,1),regs,nzcv)
        if v: msr_vectors.append(v)
for (imm,rot) in [(0xf0,4),(0x80,4),(0x30,4)]:        # MSR CPSR_f, #imm
    v=vec(msr_imm_enc(0,8,rot,imm),[0]*15,(0,0,0,0))
    if v: msr_vectors.append(v)
print(f"generated {len(msr_vectors)} MSR vectors", file=sys.stderr)
if len(sys.argv) > 5:
    json.dump({"arch":"a32","group":"msr","oracle":"unicorn-2.1.4","vectors":msr_vectors},
              open(sys.argv[5],"w"))

# ---- Media: CLZ / SXTB·UXTB·SXTH·UXTH / REV·REV16 / UBFX·SBFX / BFI·BFC ----
media_vectors=[]
mvals2=[0,1,0xffffffff,0x80000000,0x40000000,0x00010000,0xdeadbeef,0x0000ff80,0x12345678,0x000000ff,0xabcd1234]
def emit_media(word, r1=0, rd_init=0):
    regs=[0]*15; regs[1]=r1; regs[0]=rd_init; regs[2]=0x5a5a5a5a
    v=vec(word, regs, (0,0,0,0))
    if v: media_vectors.append(v)
for r1 in mvals2:
    emit_media((0xe<<28)|(0x16<<20)|(0xf<<16)|(0<<12)|(0xf<<8)|(1<<4)|1, r1)          # CLZ r0,r1
    for op in (0x6a,0x6e,0x6b,0x6f):                                                   # SXTB/UXTB/SXTH/UXTH
        for rot in (0,1,2,3):
            emit_media((0xe<<28)|(op<<20)|(0xf<<16)|(0<<12)|(rot<<10)|(0b0111<<4)|1, r1)
    emit_media((0xe<<28)|(0x6b<<20)|(0xf<<16)|(0<<12)|(0xf<<8)|(0b0011<<4)|1, r1)      # REV r0,r1
    emit_media((0xe<<28)|(0x6b<<20)|(0xf<<16)|(0<<12)|(0xf<<8)|(0b1011<<4)|1, r1)      # REV16 r0,r1
    for (lsb,wm1) in [(0,7),(4,7),(8,15),(0,31),(16,15),(3,4)]:                        # UBFX/SBFX
        emit_media((0xe<<28)|(0b0111111<<21)|(wm1<<16)|(0<<12)|(lsb<<7)|(0b101<<4)|1, r1)
        emit_media((0xe<<28)|(0b0111101<<21)|(wm1<<16)|(0<<12)|(lsb<<7)|(0b101<<4)|1, r1)
    for (lsb,msb) in [(0,7),(8,15),(4,12),(0,31)]:                                     # BFI r0,r1 / BFC r0
        emit_media((0xe<<28)|(0b0111110<<21)|(msb<<16)|(0<<12)|(lsb<<7)|(0b001<<4)|1, r1, rd_init=0xffffffff)
        emit_media((0xe<<28)|(0b0111110<<21)|(msb<<16)|(0<<12)|(lsb<<7)|(0b001<<4)|0xf, r1, rd_init=0xffffffff)
print(f"generated {len(media_vectors)} MEDIA vectors", file=sys.stderr)
if len(sys.argv) > 6:
    json.dump({"arch":"a32","group":"media","oracle":"unicorn-2.1.4","vectors":media_vectors},
              open(sys.argv[6],"w"))

# ---- VFP data-movement (bit-exact): VMOV/VABS/VNEG/VLDR/VSTR/VPUSH/VPOP ----
SREGN=[UC_ARM_REG_S0+i for i in range(32)]
def run_vfp(word, regs, sregs, premem=None):
    mu=Uc(UC_ARCH_ARM, UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE,0x1000); mu.mem_map(DATA,0x1000)
    mu.reg_write(UC_ARM_REG_C1_C0_2, 0x00f00000)     # CPACR: enable CP10/CP11
    mu.reg_write(UC_ARM_REG_FPEXC, 0x40000000)       # FPEXC.EN
    mu.reg_write(UC_ARM_REG_FPSCR, 0)                # pin FZ=0,DN=0,RMode=RNE
    mu.mem_write(CODE, struct.pack('<I',word))
    if premem is not None: mu.mem_write(WIN_LO, bytes(premem))
    for i,r in enumerate(REGS): mu.reg_write(r, regs[i]&0xffffffff)
    for i in range(32): mu.reg_write(SREGN[i], sregs[i]&0xffffffff)
    mu.reg_write(UC_ARM_REG_CPSR, 0x13)
    try: mu.emu_start(CODE,CODE+4,count=1)
    except UcError: return None
    out=[mu.reg_read(r)&0xffffffff for r in REGS]
    outs=[mu.reg_read(SREGN[i])&0xffffffff for i in range(32)]
    pc=mu.reg_read(UC_ARM_REG_PC)&0xffffffff
    postmem=list(mu.mem_read(WIN_LO,WIN_HI-WIN_LO)) if premem is not None else None
    outf=mu.reg_read(UC_ARM_REG_FPSCR)&0xffffffff
    return out,outs,pc,postmem,outf
def vmov_s_r(sn,rt): return 0xEE000A10|((sn>>1)<<16)|(rt<<12)|((sn&1)<<7)
def vmov_r_s(rt,sn): return 0xEE100A10|((sn>>1)<<16)|(rt<<12)|((sn&1)<<7)
def vmov_f32(sd,sm): return 0xEEB00A40|((sd>>1)<<12)|((sd&1)<<22)|((sm>>1))|((sm&1)<<5)
def vabs_f32(sd,sm): return 0xEEB00AC0|((sd>>1)<<12)|((sd&1)<<22)|((sm>>1))|((sm&1)<<5)
def vneg_f32(sd,sm): return 0xEEB10A40|((sd>>1)<<12)|((sd&1)<<22)|((sm>>1))|((sm&1)<<5)
def vldr_s(sd,rn,imm8): return 0xED900A00|(rn<<16)|((sd>>1)<<12)|((sd&1)<<22)|(imm8&0xff)
def vstr_s(sd,rn,imm8): return 0xED800A00|(rn<<16)|((sd>>1)<<12)|((sd&1)<<22)|(imm8&0xff)
def vpush(n): return 0xED2D0A00|(n&0xff)
def vpop(n):  return 0xECBD0A00|(n&0xff)
SVALS=[0x00000000,0x3f800000,0xbf800000,0x40490fdb,0x7f800000,0xff800000,0x7fc00000,0x00000001,0x80000000,0xdeadbeef,0x12345678,0xc0000000]
vfp_vectors=[]
def emit_vfp(word, mem=False):
    regs=[0]*15; regs[1]=WIN_LO+0x10; regs[13]=WIN_LO+0x30; regs[3]=0xA5A5F00D
    sregs=[random.choice(SVALS) for _ in range(32)]
    premem=[((0x11+i*5)&0xff) for i in range(WIN_HI-WIN_LO)] if mem else None
    r=run_vfp(word,regs,sregs,premem)
    if r is None: return
    out,outs,pc,postmem,outf=r
    v={"insn":word,"in_regs":[x&0xffffffff for x in regs],"in_nzcv":[0,0,0,0],"in_sregs":sregs,
       "out_regs":out,"out_pc":pc,"out_nzcv":[0,0,0,0],"out_sregs":outs,"out_fpscr":outf}
    if mem: v["mem_base"]=WIN_LO; v["pre_mem"]=premem; v["post_mem"]=postmem
    vfp_vectors.append(v)
for sn in (0,1,5,8,15,31):
    emit_vfp(vmov_s_r(sn,3)); emit_vfp(vmov_r_s(2,sn))
for (sd,sm) in [(0,1),(4,9),(2,2),(31,0),(7,16)]:
    emit_vfp(vmov_f32(sd,sm)); emit_vfp(vabs_f32(sd,sm)); emit_vfp(vneg_f32(sd,sm))
for sd in (0,1,6,15):
    for imm in (0,2,4,8): emit_vfp(vldr_s(sd,1,imm),mem=True); emit_vfp(vstr_s(sd,1,imm),mem=True)
for n in (1,2,4): emit_vfp(vpush(n),mem=True); emit_vfp(vpop(n),mem=True)

def vcmp(sd,sm):  return 0xEEB40A40|((sd>>1)<<12)|((sd&1)<<22)|((sm>>1))|((sm&1)<<5)
def vcmpe(sd,sm): return 0xEEB40AC0|((sd>>1)<<12)|((sd&1)<<22)|((sm>>1))|((sm&1)<<5)
def vcmp0(sd):    return 0xEEB50A40|((sd>>1)<<12)|((sd&1)<<22)
# VCMP needs specific FP values in S regs; set s0..s5 to interesting patterns
def emit_vcmp(word, a, b):
    regs=[0]*15
    sregs=[0]*32; sregs[2]=a; sregs[3]=b; sregs[4]=a; sregs[5]=b
    r=run_vfp(word, regs, sregs)
    if r is None: return
    out,outs,pc,postmem,outf=r
    vfp_vectors.append({"insn":word,"in_regs":[0]*15,"in_nzcv":[0,0,0,0],"in_sregs":sregs,
        "out_regs":out,"out_pc":pc,"out_nzcv":[0,0,0,0],"out_sregs":outs,"out_fpscr":outf})
FPV=[0x00000000,0x80000000,0x3f800000,0xbf800000,0x40490fdb,0xc0490fdb,0x7f800000,0xff800000,0x7fc00000,0x00800000,0x7f7fffff]
for a in FPV:
    for b in FPV:
        emit_vcmp(vcmp(2,3), a, b)
        emit_vcmp(vcmpe(4,5), a, b)
    emit_vcmp(vcmp0(2), a, 0)


# VFP arithmetic Sd=s4, Sn=s0, Sm=s2 (validates the Sei.Float wiring end-to-end)
for (op,enc) in [("vadd",0xEE302A01),("vsub",0xEE302A41),("vmul",0xEE202A01),("vdiv",0xEE802A01)]:
    for _ in range(40):
        emit_vfp(enc)
for _ in range(60): emit_vfp(0xEEB12AC1)  # vsqrt.f32 s4,s2
# double-precision (CP11): D0-D15 alias S0-S31, so the S-reg checker validates them
for enc in [0xEE304B02,0xEE304B42,0xEE204B02,0xEE804B02,0xEEB04B42,0xEEB04BC2,0xEEB14B42]:
    for _ in range(40): emit_vfp(enc)          # VADD/VSUB/VMUL/VDIV/VMOV/VABS/VNEG.F64
for _ in range(60): emit_vfp(0xEEB14BC2)       # VSQRT.F64 d4,d2
for sd_enc in [0xED914B00,0xED814B00]:         # VLDR.64/VSTR.64 d4,[r1,#0]
    for _ in range(20): emit_vfp(sd_enc, mem=True)
for _ in range(20): emit_vfp(0xEC914B04, mem=True)  # VLDMIA r1!, {d4,d5} (2 dregs)
for enc in [0xEEB81A41,0xEEB81AC1,0xEEBC1AC1,0xEEBD1AC1,0xEEB72AC1,0xEEB71BC2,
            0xEEB82B41,0xEEB82BC1,0xEEBC1BC2,0xEEBD1BC2,
            0xEEBC1A41,0xEEBD1A41,0xEEBC1B42,0xEEBD1B42]:   # VCVT + VCVTR (round to nearest)
    for _ in range(30): emit_vfp(enc)
for enc in [0xEE002A01,0xEE002A41,0xEE102A01,0xEE102A41,0xEE202A41,   # VMLA/VMLS/VNMLS/VNMLA/VNMUL.F32
            0xEE002B02,0xEE002B42,0xEE102B02,0xEE102B42,0xEE202B42]:  # F64 variants
    for _ in range(30): emit_vfp(enc)
for enc in [0xEEA02A01,0xEEA02A41,0xEE902A01,0xEE902A41,      # VFMA/VFMS/VFNMS/VFNMA.F32
            0xEEA04B02,0xEEA04B42,0xEE904B02,0xEE904B42]:      # F64 variants
    for _ in range(30): emit_vfp(enc)
def _vmovimm_s(i): return (0xe<<28)|(0b1110<<24)|(0b1011<<20)|(((i>>4)&0xf)<<16)|(2<<12)|(0b101<<9)|(i&0xf)
def _vmovimm_d(i): return (0xe<<28)|(0b1110<<24)|(0b1011<<20)|(((i>>4)&0xf)<<16)|(4<<12)|(0b101<<9)|(1<<8)|(i&0xf)
for i in range(256):
    emit_vfp(_vmovimm_s(i)); emit_vfp(_vmovimm_d(i))
for enc in [0xEC410B14,0xEC510B14,0xEC410A12,0xEC510A12]:  # VMOV core-pair<->D/S
    for _ in range(25): emit_vfp(enc)
for enc in [0xEEB22A41,0xEEB22AC1,0xEEB32A41,0xEEB32AC1]:  # VCVTB/VCVTT (F16<->F32)
    for _ in range(60): emit_vfp(enc)
for _ in range(15): emit_vfp(0xeef02a10)   # VMRS r2,fpsid
for _ in range(15): emit_vfp(0xeee02a10)   # VMSR fpsid,r2 (no-op)
for enc in [0xEE002B10,0xEE202B10,0xEE112B10,0xEE312B10]:  # VMOV.32 Dd[0/1],Rt / Rt,Dd[0/1]
    for _ in range(20): emit_vfp(enc)

def _vcvt_fixed(toF,signed,sx32,fbits,sz,vd=1,D=0):
    size=32 if sx32 else 16; imm=size-fbits
    opc2=(0b1110 if toF else 0b1010)|(0 if signed else 1)
    return (0xe<<28)|(0b1110<<24)|(0b1011<<20)|(D<<22)|(opc2<<16)|(vd<<12)|(0b101<<9)|(sz<<8)|(int(sx32)<<7)|(1<<6)|((imm&1)<<5)|((imm>>1)&0xf)
for toF in (False,True):
    for signed in (False,True):
        for sx32 in (False,True):
            for fbits in ([1,8,15,16] if not sx32 else [1,16,31,32]):
                for sz in (0,1):
                    for _ in range(8): emit_vfp(_vcvt_fixed(toF,signed,sx32,fbits,sz))









print(f"generated {len(vfp_vectors)} VFP vectors", file=sys.stderr)
if len(sys.argv) > 7:
    json.dump({"arch":"a32","group":"vfp","oracle":"unicorn-2.1.4","vectors":vfp_vectors},
              open(sys.argv[7],"w"))

# ---- A32 Branch: B / BL / BX / BLX register ----
def b_enc(cond, link, imm24): return (cond<<28)|((0b1010|link)<<24)|(imm24&0xffffff)
def bx_enc(cond, rm):  return (cond<<28)|0x12FFF10|(rm&0xf)
def blx_enc(cond, rm): return (cond<<28)|0x12FFF30|(rm&0xf)
COND_AL = 0xe
branch_vectors = []
def bvec(word, regs, nzcv=(0,0,0,0)):
    r = run_one(word, regs, nzcv)
    if r is None: return None
    out, pc, onzcv = r
    regs_s = [x & 0xffffffff for x in regs]
    return {"insn": word, "in_regs": regs_s, "in_nzcv": list(nzcv),
            "out_regs": out, "out_pc": pc, "out_nzcv": list(onzcv)}

# B forward/backward (AL condition)
for imm24 in [1, 2, 5, 0x20, 0xFFFFFE]:  # 0xFFFFFE = -2 → target = CODE
    v = bvec(b_enc(COND_AL, 0, imm24), [0]*15)
    if v: branch_vectors.append(v)
# BL: LR gets set to CODE+4, PC changes
for imm24 in [1, 4, 0x10]:
    v = bvec(b_enc(COND_AL, 1, imm24), [0]*15)
    if v: branch_vectors.append(v)
# Conditional branches: BEQ, BNE, BLT, BGT with various NZCV
for (cond, nzcv_taken, nzcv_nottaken) in [
    (0x0, (0,1,0,0), (0,0,0,0)),   # BEQ: Z=1 taken, Z=0 not
    (0x1, (0,0,0,0), (0,1,0,0)),   # BNE: Z=0 taken, Z=1 not
    (0x4, (0,0,0,0), (0,0,1,0)),   # BMI / N=1 taken — actually cond 4 is MI (N=1)
    # cond 4 is MI: N=1 taken
    (0x5, (0,0,0,0), (1,0,0,0)),   # BPL: N=0 taken, N=1 not
    (0xb, (1,0,0,1), (0,0,0,0)),   # BLT: N≠V taken (N=1,V=1 → not taken; N=1,V=0 → taken)
]:
    for imm24 in [1, 3]:
        v = bvec(b_enc(cond, 0, imm24), [0]*15, nzcv_taken)
        if v: branch_vectors.append(v)
        v = bvec(b_enc(cond, 0, imm24), [0]*15, nzcv_nottaken)
        if v: branch_vectors.append(v)
# BX register: ARM target (bit0=0), Thumb target (bit0=1)
for rm in [2, 3, 5]:
    regs = [0]*15
    regs[rm] = CODE + 8          # ARM target, stays in ARM mode
    v = bvec(bx_enc(COND_AL, rm), regs)
    if v: branch_vectors.append(v)
    regs[rm] = CODE + 8 + 1     # Thumb target, switches to Thumb
    v = bvec(bx_enc(COND_AL, rm), regs)
    if v: branch_vectors.append(v)
# BLX register: LR = CODE+4, PC = Rm & ~1, tbit = Rm[0]
for rm in [2, 4]:
    regs = [0]*15
    regs[rm] = CODE + 8          # ARM target
    v = bvec(blx_enc(COND_AL, rm), regs)
    if v: branch_vectors.append(v)
    regs[rm] = CODE + 8 + 1     # Thumb target
    v = bvec(blx_enc(COND_AL, rm), regs)
    if v: branch_vectors.append(v)
print(f"generated {len(branch_vectors)} BRANCH vectors", file=sys.stderr)
if len(sys.argv) > 8:
    json.dump({"arch":"a32","group":"branch","oracle":"unicorn-2.1.4","vectors":branch_vectors},
              open(sys.argv[8],"w"))

# ---- A32 LDM / STM (block data transfer) ----
def ldm_enc(P, U, W, L, rn, rlist):
    return (0xe<<28)|(0b100<<25)|(P<<24)|(U<<23)|(0<<22)|(W<<21)|(L<<20)|(rn<<16)|(rlist&0xffff)
def run_block(word, regs, premem):
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM | UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE, 0x1000); mu.mem_map(DATA, 0x1000)
    mu.mem_write(CODE, struct.pack('<I', word))
    mu.mem_write(WIN_LO, bytes(premem))
    for i, r in enumerate(REGS): mu.reg_write(r, regs[i] & 0xffffffff)
    mu.reg_write(UC_ARM_REG_CPSR, 0x13)
    try: mu.emu_start(CODE, CODE+4, count=1)
    except UcError: return None
    out = [mu.reg_read(r) & 0xffffffff for r in REGS]
    postmem = list(mu.mem_read(WIN_LO, WIN_HI-WIN_LO))
    return out, mu.reg_read(UC_ARM_REG_PC) & 0xffffffff, postmem
def bvec_ldm(word, regs, premem):
    regs_s = [x & 0xffffffff for x in regs]
    r = run_block(word, regs_s, premem)
    if r is None: return None
    out, pc, postmem = r
    return {"insn": word, "in_regs": regs_s, "in_nzcv": [0,0,0,0],
            "mem_base": WIN_LO, "pre_mem": premem,
            "out_regs": out, "out_pc": pc, "out_nzcv": [0,0,0,0], "post_mem": postmem}
ldm_vectors = []
STORE_VALS = [0x11111111, 0x22222222, 0x33333333, 0x44444444,
              0x55555555, 0x66666666, 0x77777777, 0x88888888]
PREMEM = [(0xA0+i) & 0xff for i in range(WIN_HI-WIN_LO)]  # known pattern for LDM
for rlist in [0x04, 0x0C, 0x3C, 0xFC]:      # r2 only; r2-r3; r2-r5; r2-r7
    for (P, U, W) in [(0,1,0),(0,1,1),(1,1,1),(1,0,1)]:  # IA, IA!, IB!, DB!
        if P==0 and W==1 and U==0: continue   # post-decrement writeback = unpredictable in A32
        # LDM: load from BASE into rlist registers (rn=r1, rlist excludes r1)
        regs = [0]*15; regs[1] = BASE
        v = bvec_ldm(ldm_enc(P,U,W,1,1,rlist), regs, PREMEM)
        if v: ldm_vectors.append(v)
        # STM: store rlist registers (r2-r7) to BASE; r1 must stay as BASE
        regs = [0]*15
        for i in range(8): regs[i] = STORE_VALS[i]   # r0..r7 get store values
        regs[1] = BASE                                 # r1 = base register (overrides STORE_VALS[1])
        v = bvec_ldm(ldm_enc(P,U,W,0,1,rlist), regs, PREMEM)
        if v: ldm_vectors.append(v)
# Larger rlist with more varied base offsets; only use rlists that exclude r1 (bit 1)
for (rlist, base_off) in [(0x00F4, 0), (0x00FC, 0), (0x5554, 0), (0x00F4, -0x10)]:
    premem2 = [(0xB0+i) & 0xff for i in range(WIN_HI-WIN_LO)]
    # LDM: rn=r1 at BASE+base_off; rlist excludes r1
    regs_ld = [0]*15; regs_ld[1] = BASE + base_off
    v = bvec_ldm(ldm_enc(0,1,0,1,1,rlist), regs_ld, premem2)
    if v: ldm_vectors.append(v)
    # STM: rn=r1 at BASE+base_off; other regs have store values
    regs_st = [0]*15
    for i in range(8): regs_st[i] = STORE_VALS[i]
    regs_st[1] = BASE + base_off
    v = bvec_ldm(ldm_enc(0,1,0,0,1,rlist), regs_st, premem2)
    if v: ldm_vectors.append(v)
print(f"generated {len(ldm_vectors)} LDM vectors", file=sys.stderr)
if len(sys.argv) > 9:
    json.dump({"arch":"a32","group":"ldm","oracle":"unicorn-2.1.4","vectors":ldm_vectors},
              open(sys.argv[9],"w"))
