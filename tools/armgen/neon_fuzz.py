#!/usr/bin/env python3
# NEON-space fuzzer: random words across the Advanced SIMD encoding spaces → Unicorn
# (subprocess-isolated so a JIT SIGILL doesn't abort the run) → corpus. arm_vec_check
# --stats then asserts every Unicorn-accepted word is decode-correct OR fail-closed.
import json, struct, sys, random, subprocess, os
random.seed(99)
CODE=0x10000; DATA=0x20000; WIN_LO=0x20020; WIN_HI=0x20060
# random words biased into the SIMD spaces
def randword():
    sp=random.random()
    if sp<0.45: return 0xF2000000|random.getrandbits(25)          # NEON dp (F2/F3)
    if sp<0.60: return 0xF3000000|random.getrandbits(24)
    if sp<0.78: return 0xF4000000|random.getrandbits(24)          # NEON ld/st
    return 0xEE000000|(random.getrandbits(8)<<16)|0x0A00|random.getrandbits(8)  # VFP/VDUP-ish
WORKER=r'''
import sys,struct,json
from unicorn import *; from unicorn.arm_const import *
CODE=0x10000; DATA=0x20000; WIN_LO=0x20020; WIN_HI=0x20060
SREG=[UC_ARM_REG_S0+i for i in range(32)]; REGS=[UC_ARM_REG_R0+i for i in range(13)]+[UC_ARM_REG_SP,UC_ARM_REG_LR]
out=[]
for line in sys.stdin:
    w=int(line); 
    try:
        mu=Uc(UC_ARCH_ARM,UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN); mu.mem_map(CODE,0x1000); mu.mem_map(DATA,0x1000)
        mu.reg_write(UC_ARM_REG_C1_C0_2,0x00f00000); mu.reg_write(UC_ARM_REG_FPEXC,0x40000000); mu.reg_write(UC_ARM_REG_FPSCR,0)
        sr=[ (0x11111111*(i+3))&0xffffffff for i in range(32)]
        for i in range(32): mu.reg_write(SREG[i],sr[i])
        regs=[0]*15; regs[1]=WIN_LO+0x10; regs[3]=16
        for i in range(15): mu.reg_write(REGS[i],regs[i])
        pm=[((0x13+i*7)&0xff) for i in range(WIN_HI-WIN_LO)]; mu.mem_write(WIN_LO,bytes(pm))
        mu.mem_write(CODE,struct.pack("<I",w)); mu.reg_write(UC_ARM_REG_CPSR,0x13)
        mu.emu_start(CODE,CODE+4,count=1)
        if mu.reg_read(UC_ARM_REG_PC)!=CODE+4: continue        # branch/abort → skip
        outs=[mu.reg_read(SREG[i])&0xffffffff for i in range(32)]
        oregs=[mu.reg_read(REGS[i])&0xffffffff for i in range(15)]
        post=list(mu.mem_read(WIN_LO,WIN_HI-WIN_LO))
        out.append({"insn":w,"in_regs":regs,"in_nzcv":[0,0,0,0],"in_sregs":sr,"out_regs":oregs,
                    "out_pc":CODE+4,"out_nzcv":[0,0,0,0],"out_sregs":outs,"out_fpscr":mu.reg_read(UC_ARM_REG_FPSCR)&0xffffffff,
                    "mem_base":WIN_LO,"pre_mem":pm,"post_mem":post})
    except UcError: continue
sys.stdout.write(json.dumps(out))
'''
open('/tmp/nfworker.py','w').write(WORKER)
def fixrn(w):
    # F4 (NEON ld/st) and EEx VLDR/VSTR/VLDM use Rn=bits[19:16]; pin to r1 (window)
    if (w>>24)&0xff==0xf4 or ((w>>24)&0xf==0xe and (w>>25)&7==0b110):
        w=(w & ~(0xf<<16)) | (1<<16)
    return w
words=list({fixrn(randword()) for _ in range(int(sys.argv[2]) if len(sys.argv)>2 else 40000)})
vecs=[]; B=40
for i in range(0,len(words),B):
    batch=words[i:i+B]
    try:
        r=subprocess.run([sys.executable,'/tmp/nfworker.py'],input="\n".join(map(str,batch)),
                         capture_output=True,text=True,timeout=60)
        if r.returncode==0 and r.stdout: vecs.extend(json.loads(r.stdout))
    except Exception: continue   # batch crashed (SIGILL) — skip it
print(f"fuzz: {len(words)} words → {len(vecs)} Unicorn-accepted", file=sys.stderr)
json.dump({"arch":"a32","group":"neon-fuzz","vectors":vecs}, open(sys.argv[1],'w'))
