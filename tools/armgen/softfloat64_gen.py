#!/usr/bin/env python3
# OFFLINE oracle: binary64 op vectors from Unicorn VADD/VSUB/VMUL/VDIV/VSQRT.F64.
# 64-bit values stored as hex strings (JSON numbers lose precision above 2^53).
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *
from capstone import *
random.seed(13); md=Cs(CS_ARCH_ARM,CS_MODE_ARM); CODE=0x10000
# Dd=D4, Dn=D0, Dm=D2
VADD=0xEE304B02; VSUB=0xEE304B42; VMUL=0xEE204B02; VDIV=0xEE804B02; VSQRT=0xEEB14BC2
for nm,w in [("vadd",VADD),("vsub",VSUB),("vmul",VMUL),("vdiv",VDIV),("vsqrt",VSQRT)]:
    d=next(md.disasm(struct.pack('<I',w),0x1000),None); print(f"{nm}: {d.mnemonic+' '+d.op_str if d else '?'}", file=sys.stderr)
def run(op,a,b):
    mu=Uc(UC_ARCH_ARM,UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN); mu.mem_map(CODE,0x1000)
    mu.reg_write(UC_ARM_REG_C1_C0_2,0x00f00000); mu.reg_write(UC_ARM_REG_FPEXC,0x40000000); mu.reg_write(UC_ARM_REG_FPSCR,0)
    mu.mem_write(CODE,struct.pack('<I',op)); mu.reg_write(UC_ARM_REG_D0,a); mu.reg_write(UC_ARM_REG_D2,b)
    mu.reg_write(UC_ARM_REG_CPSR,0x13)
    try: mu.emu_start(CODE,CODE+4,count=1)
    except UcError: return None
    return mu.reg_read(UC_ARM_REG_D4)&0xffffffffffffffff
EDGE=[0,1<<63,0x3ff0000000000000,0xbff0000000000000,0x4000000000000000,0x7ff0000000000000,
      0xfff0000000000000,0x7ff8000000000000,0x7ff0000000000001,0x0000000000000001,
      0x000fffffffffffff,0x0010000000000000,0x7fefffffffffffff,0x400921fb54442d18,
      0x3fd5555555555555,0xc000000000000000,0x3cb0000000000000,0x4350000000000000]
vals=EDGE+[random.getrandbits(64) for _ in range(120)]
vecs=[]
for nm,op in [("add",VADD),("sub",VSUB),("mul",VMUL),("div",VDIV)]:
    for a in EDGE:
        for b in EDGE:
            r=run(op,a,b)
            if r is not None: vecs.append({"op":nm,"fmt":"f64","a":hex(a),"b":hex(b),"r":hex(r)})
    for _ in range(1500):
        a=random.choice(vals); b=random.choice(vals); r=run(op,a,b)
        if r is not None: vecs.append({"op":nm,"fmt":"f64","a":hex(a),"b":hex(b),"r":hex(r)})
for a in vals:
    r=run(VSQRT,0,a)
    if r is not None: vecs.append({"op":"sqrt","fmt":"f64","a":hex(a),"b":"0x0","r":hex(r)})
print(f"generated {len(vecs)} binary64 vectors", file=sys.stderr)
json.dump({"oracle":"unicorn-2.1.4","fmt":"binary64","vectors":vecs}, open(sys.argv[1] if len(sys.argv)>1 else '/tmp/sf64.json','w'))
