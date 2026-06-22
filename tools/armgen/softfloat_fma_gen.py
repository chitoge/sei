#!/usr/bin/env python3
# OFFLINE oracle: fused multiply-add vectors (a*b+c) from Unicorn VFMA.F32 s4,s0,s2.
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *
random.seed(23); CODE=0x10000; VFMA=0xEEA02A01
def run(a,b,c):
    mu=Uc(UC_ARCH_ARM,UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN); mu.mem_map(CODE,0x1000)
    mu.reg_write(UC_ARM_REG_C1_C0_2,0x00f00000); mu.reg_write(UC_ARM_REG_FPEXC,0x40000000); mu.reg_write(UC_ARM_REG_FPSCR,0)
    mu.mem_write(CODE,struct.pack('<I',VFMA))
    mu.reg_write(UC_ARM_REG_S0,a); mu.reg_write(UC_ARM_REG_S2,b); mu.reg_write(UC_ARM_REG_S4,c)
    mu.reg_write(UC_ARM_REG_CPSR,0x13)
    try: mu.emu_start(CODE,CODE+4,count=1)
    except UcError: return None
    return mu.reg_read(UC_ARM_REG_S4)&0xffffffff
EDGE=[0,0x80000000,0x3f800000,0xbf800000,0x40000000,0xc0000000,0x7f800000,0xff800000,0x7fc00000,
      0x00000001,0x007fffff,0x00800000,0x7f7fffff,0x40490fdb,0x33800000,0x4b800000,0x3f000000]
vals=EDGE+[random.getrandbits(32) for _ in range(120)]
vecs=[]
for a in EDGE:
    for b in EDGE:
        for c in [0,0x3f800000,0xbf800000,0x40000000,0x7fc00000,0x7f800000,0xffc00000,0x7f800001,0xff800000,0x80000000]:
            r=run(a,b,c)
            if r is not None: vecs.append({"op":"fma","a":hex(a),"b":hex(b),"c":hex(c),"r":hex(r)})
for _ in range(4000):
    a=random.choice(vals); b=random.choice(vals); c=random.choice(vals); r=run(a,b,c)
    if r is not None: vecs.append({"op":"fma","a":hex(a),"b":hex(b),"c":hex(c),"r":hex(r)})
print(f"generated {len(vecs)} fma vectors", file=sys.stderr)
json.dump({"oracle":"unicorn-2.1.4","fmt":"fma32","vectors":vecs}, open(sys.argv[1] if len(sys.argv)>1 else '/tmp/fma.json','w'))
