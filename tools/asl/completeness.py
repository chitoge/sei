#!/usr/bin/env python3
# Completeness check against ARM's BSD-licensed AARCHMRS encoding index: for every
# canonical A32 instruction, synthesize a representative encoding, keep the ones
# Unicorn accepts, and emit a corpus tagged with the ARM instruction name so the
# Lean decoder's coverage can be measured per-instruction.
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *
random.seed(7)
import os
FPFILL=int(os.environ.get("FPFILL","0x3f800000"),0)  # S-reg fill; set fractional to stress FP rounding
INSTR=json.load(open(sys.argv[1] if len(sys.argv)>1 else '/tmp/Instructions.json'))
a32=[n for n in INSTR['instructions'] if n.get('name')=='A32'][0]
def kids(n): return n.get('children') or []
def leaves(n, acc):
    if not kids(n):
        if n.get('encoding'): acc.append(n)
    else:
        for c in kids(n): leaves(c, acc)
LV=[]; leaves(a32, LV)
print(f"A32 leaves: {len(LV)}", file=sys.stderr)

REGF={'Rn','Rt','Rd','Rm','Rs','Ra','RdHi','RdLo','Rt2','Rn1','Vd','Vn','Vm'}
def synth(leaf):
    """Build a representative 32-bit word from the leaf's Encodeset."""
    word=0; xmask=0  # xmask: bits NOT pinned by the encoding
    # default all variable bits to 0
    fields=[]
    for f in leaf['encoding']['values']:
        r=f['range']; start=r['start']; width=r['width']
        val=f['value']['value'].strip("'")
        name=f.get('name')
        fields.append((name,start,width,val))
    # assign each bit
    bits=['0']*32
    pinned=[False]*32
    for name,start,width,val in fields:
        for i in range(width):
            b=start+width-1-i  # val is MSB-first
            ch=val[i]
            if ch in '01':
                bits[b]=ch; pinned[b]=True
    # fill variable named fields with safe values
    def setfield(start,width,v):
        for i in range(width):
            b=start+i
            if not pinned[b]: bits[b]=str((v>>i)&1)
    for name,start,width,val in fields:
        if any(c in 'x' for c in val):
            if name=='cond': setfield(start,width,0xE)             # AL
            elif name in REGF: setfield(start,width, {'Rn':1,'Rt':2,'Rd':0,'Rm':3,'Rs':4,'Ra':5,'RdHi':6,'RdLo':7,'Rt2':3,'Vd':0,'Vn':1,'Vm':2}.get(name,1))
            elif name in ('imm24','imm12','imm8','imm5','imm4','imm16','imm4H','imm4L'): setfield(start,width,0)
            else: setfield(start,width,0)
    w=0
    for b in range(32):
        if bits[b]=='1': w|=(1<<b)
    return w
words={}
for lf in LV:
    try: w=synth(lf)
    except Exception: continue
    words.setdefault(w, lf['name'])  # name per representative word

# run each through Unicorn; keep accepted
CODE=0x10000; DATA=0x20000; WIN_LO=0x20020; WIN_HI=0x20060
REGS=[UC_ARM_REG_R0+i for i in range(13)]+[UC_ARM_REG_SP,UC_ARM_REG_LR]
SREG=[UC_ARM_REG_S0+i for i in range(32)]
def run(word):
    mu=Uc(UC_ARCH_ARM,UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN)
    mu.mem_map(CODE,0x1000); mu.mem_map(DATA,0x10000)
    mu.reg_write(UC_ARM_REG_C1_C0_2,0x00f00000); mu.reg_write(UC_ARM_REG_FPEXC,0x40000000); mu.reg_write(UC_ARM_REG_FPSCR,0)
    mu.mem_write(CODE,struct.pack('<I',word)); 
    pm=[((0x10+i*7)&0xff) for i in range(WIN_HI-WIN_LO)]; mu.mem_write(WIN_LO,bytes(pm))
    regs=[(DATA+0x10+i*0x40)&0xffffffff for i in range(15)]; regs[13]=DATA+0x40
    for i,r in enumerate(REGS): mu.reg_write(r,regs[i])
    for i in range(32): mu.reg_write(SREG[i], FPFILL)
    mu.reg_write(UC_ARM_REG_CPSR,0x13)
    try: mu.emu_start(CODE,CODE+4,count=1)
    except UcError: return None,regs,pm
    cp=mu.reg_read(UC_ARM_REG_CPSR)
    out=[mu.reg_read(r)&0xffffffff for r in REGS]
    outs=[mu.reg_read(SREG[i])&0xffffffff for i in range(32)]
    return (out,outs,mu.reg_read(UC_ARM_REG_PC)&0xffffffff,list(mu.mem_read(WIN_LO,WIN_HI-WIN_LO)),
            [(cp>>31)&1,(cp>>30)&1,(cp>>29)&1,(cp>>28)&1], mu.reg_read(UC_ARM_REG_FPSCR)&0xffffffff), regs, pm
vecs=[]; accepted=0; namemap={}
for w,name in words.items():
    r,regs,pm=run(w)
    if r is None: continue
    accepted+=1; out,outs,pc,postmem,nzcv,outf=r
    namemap[w]=name
    vecs.append({"insn":w,"name":name,"in_regs":regs,"in_nzcv":[0,0,0,0],"in_sregs":[FPFILL]*32,
        "mem_base":WIN_LO,"pre_mem":pm,"out_regs":out,"out_pc":pc,"out_nzcv":nzcv,
        "out_sregs":outs,"post_mem":postmem,"out_fpscr":outf})
print(f"representative words: {len(words)}, Unicorn-accepted: {accepted}", file=sys.stderr)
json.dump({"arch":"a32","group":"completeness","oracle":"unicorn+AARCHMRS-2025-09","vectors":vecs}, open(sys.argv[2] if len(sys.argv)>2 else '/tmp/complete.json','w'))
