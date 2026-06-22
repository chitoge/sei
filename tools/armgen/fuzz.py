#!/usr/bin/env python3
# OFFLINE differential fuzzer (Unicorn oracle): emit a corpus of random A32
# instructions that Unicorn accepts, with pre/post state, for the Lean checker's
# --stats mode to measure decode coverage + correctness over the real ISA.
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *
random.seed(int(sys.argv[2]) if len(sys.argv)>2 else 1)
N=int(sys.argv[3]) if len(sys.argv)>3 else 20000
CODE=0x10000; DATA=0x20000; WIN_LO=0x20020; WIN_HI=0x20060
REGS=[UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3,UC_ARM_REG_R4,UC_ARM_REG_R5,
      UC_ARM_REG_R6,UC_ARM_REG_R7,UC_ARM_REG_R8,UC_ARM_REG_R9,UC_ARM_REG_R10,UC_ARM_REG_R11,
      UC_ARM_REG_R12,UC_ARM_REG_R13,UC_ARM_REG_R14]
SREG=[UC_ARM_REG_S0+i for i in range(32)]
FPV=[0,0x3f800000,0xbf800000,0x40490fdb,0x7f800000,0x7fc00000,0x00800000,0xdeadbeef]
def run(word, regs, sregs, premem):
    mu=Uc(UC_ARCH_ARM, UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE,0x1000); mu.mem_map(DATA,0x10000)
    mu.reg_write(UC_ARM_REG_C1_C0_2,0x00f00000); mu.reg_write(UC_ARM_REG_FPEXC,0x40000000); mu.reg_write(UC_ARM_REG_FPSCR,0)
    mu.mem_write(CODE, struct.pack('<I',word)); mu.mem_write(WIN_LO, bytes(premem))
    for i,r in enumerate(REGS): mu.reg_write(r, regs[i]&0xffffffff)
    for i in range(32): mu.reg_write(SREG[i], sregs[i]&0xffffffff)
    mu.reg_write(UC_ARM_REG_CPSR, 0x13)
    try: mu.emu_start(CODE,CODE+4,count=1)
    except UcError: return None
    out=[mu.reg_read(r)&0xffffffff for r in REGS]
    outs=[mu.reg_read(SREG[i])&0xffffffff for i in range(32)]
    cp=mu.reg_read(UC_ARM_REG_CPSR)
    nzcv=[(cp>>31)&1,(cp>>30)&1,(cp>>29)&1,(cp>>28)&1]
    return out, outs, mu.reg_read(UC_ARM_REG_PC)&0xffffffff, list(mu.mem_read(WIN_LO,WIN_HI-WIN_LO)), mu.reg_read(UC_ARM_REG_FPSCR)&0xffffffff, nzcv
vectors=[]; accepted=0
for _ in range(N):
    word=(0xe<<28)|random.getrandbits(28)          # cond=AL, random rest
    regs=[(DATA+0x10+(i*0x40))&0xffffffff for i in range(15)]  # point into DATA so mem ops are mapped
    regs[13]=DATA+0x40                              # sp within window for push/pop
    sregs=[random.choice(FPV) for _ in range(32)]
    premem=[((0x10+i*7)&0xff) for i in range(WIN_HI-WIN_LO)]
    r=run(word, regs, sregs, premem)
    if r is None: continue
    accepted+=1
    out,outs,pc,postmem,outf,nzcv=r
    vectors.append({"insn":word,"in_regs":regs,"in_nzcv":[0,0,0,0],"in_sregs":sregs,
        "mem_base":WIN_LO,"pre_mem":premem,"out_regs":out,"out_pc":pc,"out_nzcv":nzcv,
        "out_sregs":outs,"post_mem":postmem,"out_fpscr":outf,"out_nzcv2":nzcv})
print(f"tried {N}, Unicorn accepted {accepted}", file=sys.stderr)
json.dump({"arch":"a32","group":"fuzz","oracle":"unicorn-2.1.4","vectors":vectors}, open(sys.argv[1],"w"))
