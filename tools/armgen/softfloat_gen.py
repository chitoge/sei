#!/usr/bin/env python3
# OFFLINE oracle: generate IEEE binary32 op vectors (a,b -> result) by running a
# single VFP instruction in Unicorn, to validate Sei.Float bit-exactly.
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *
from capstone import *
random.seed(11)
md=Cs(CS_ARCH_ARM,CS_MODE_ARM)
CODE=0x10000
# VADD/VSUB/VMUL.F32 S4, S0, S2  (Sd=S4 Vd=2 D0; Sn=S0; Sm=S2 Vm=1 M0)
def enc(o1,o2,o3): return (0xe<<28)|(0b11100<<23)|(o1<<23 if False else 0)|(o2<<20)|(0<<16)|(2<<12)|(0b101<<9)|(0<<8)|(0<<7)|(o3<<6)|(0<<5)|(1)
VADD=0xEE301A01; VSUB=0xEE301A41; VMUL=0xEE201A01; VDIV=0xEE801A01
for nm,w in [("vadd",VADD),("vsub",VSUB),("vmul",VMUL),("vdiv",VDIV)]:
    d=next(md.disasm(struct.pack('<I',w),0x1000),None)
    print(f"{nm}: 0x{w:08X} -> {d.mnemonic+' '+d.op_str if d else '?'}", file=sys.stderr)
def run(op, a, b):
    mu=Uc(UC_ARCH_ARM,UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN); mu.mem_map(CODE,0x1000)
    mu.reg_write(UC_ARM_REG_C1_C0_2,0x00f00000); mu.reg_write(UC_ARM_REG_FPEXC,0x40000000); mu.reg_write(UC_ARM_REG_FPSCR,0)
    mu.mem_write(CODE,struct.pack('<I',op)); mu.reg_write(UC_ARM_REG_S0,a); mu.reg_write(UC_ARM_REG_S2,b)
    mu.reg_write(UC_ARM_REG_CPSR,0x13)
    try: mu.emu_start(CODE,CODE+4,count=1)
    except UcError: return None
    return mu.reg_read(UC_ARM_REG_S2)&0xffffffff
EDGE=[0x00000000,0x80000000,0x3f800000,0xbf800000,0x40000000,0xc0000000,0x7f800000,0xff800000,
      0x7fc00000,0x7f800001,0xffc00000,0x00000001,0x80000001,0x007fffff,0x00800000,0x80800000,
      0x7f7fffff,0xff7fffff,0x40490fdb,0x3eaaaaab,0x34000000,0x4b7fffff,0x3f7fffff,0x3f800001,
      0x33800000,0x00400000,0x49742400,0x4effffff]
def rfloat():
    r=random.getrandbits(32)
    return r
vals=EDGE+[rfloat() for _ in range(120)]
vectors=[]
for nm,op in [("add",VADD),("sub",VSUB),("mul",VMUL),("div",VDIV)]:
    pairs=[(a,b) for a in EDGE for b in EDGE] + [(random.choice(vals),random.choice(vals)) for _ in range(2000)]
    for a,b in pairs:
        r=run(op,a,b)
        if r is None: continue
        vectors.append({"op":nm,"a":a,"b":b,"r":r})
VSQRT=0xEEB11AC0
for a in EDGE+vals:
    mu=Uc(UC_ARCH_ARM,UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN); mu.mem_map(CODE,0x1000)
    mu.reg_write(UC_ARM_REG_C1_C0_2,0x00f00000); mu.reg_write(UC_ARM_REG_FPEXC,0x40000000); mu.reg_write(UC_ARM_REG_FPSCR,0)
    mu.mem_write(CODE,struct.pack('<I',VSQRT)); mu.reg_write(UC_ARM_REG_S0,a); mu.reg_write(UC_ARM_REG_CPSR,0x13)
    try: mu.emu_start(CODE,CODE+4,count=1)
    except UcError: continue
    vectors.append({"op":"sqrt","a":a,"b":0,"r":mu.reg_read(UC_ARM_REG_S2)&0xffffffff})
print(f"generated {len(vectors)} softfloat vectors", file=sys.stderr)
json.dump({"oracle":"unicorn-2.1.4","fmt":"binary32","vectors":vectors}, open(sys.argv[1] if len(sys.argv)>1 else '/tmp/sf.json','w'))
