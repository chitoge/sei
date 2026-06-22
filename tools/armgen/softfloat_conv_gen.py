#!/usr/bin/env python3
# OFFLINE oracle: VCVT conversion vectors (int↔float, f32↔f64) from Unicorn.
import json, struct, sys, random
from unicorn import *
from unicorn.arm_const import *
random.seed(17); CODE=0x10000
# (name, encoding, in_is_double, out_is_double)
CONV=[("u32_to_f32",0xEEB81A41,False,False),("i32_to_f32",0xEEB81AC1,False,False),
      ("f32_to_u32",0xEEBC1AC1,False,False),("f32_to_i32",0xEEBD1AC1,False,False),
      ("f32_to_f64",0xEEB72AC1,False,True),("f64_to_f32",0xEEB71BC2,True,False),
      ("u32_to_f64",0xEEB82B41,False,True),("i32_to_f64",0xEEB82BC1,False,True),
      ("f64_to_u32",0xEEBC1BC2,True,False),("f64_to_i32",0xEEBD1BC2,True,False),
      ("f32_to_u32r",0xEEBC1A41,False,False),("f32_to_i32r",0xEEBD1A41,False,False),
      ("f64_to_u32r",0xEEBC1B42,True,False),("f64_to_i32r",0xEEBD1B42,True,False)]
def run(enc,a,ind,outd):
    mu=Uc(UC_ARCH_ARM,UC_MODE_ARM|UC_MODE_LITTLE_ENDIAN); mu.mem_map(CODE,0x1000)
    mu.reg_write(UC_ARM_REG_C1_C0_2,0x00f00000); mu.reg_write(UC_ARM_REG_FPEXC,0x40000000); mu.reg_write(UC_ARM_REG_FPSCR,0)
    mu.mem_write(CODE,struct.pack('<I',enc))
    if ind: mu.reg_write(UC_ARM_REG_D2,a)
    else: mu.reg_write(UC_ARM_REG_S2,a)
    mu.reg_write(UC_ARM_REG_CPSR,0x13)
    try: mu.emu_start(CODE,CODE+4,count=1)
    except UcError: return None
    if outd: return mu.reg_read(UC_ARM_REG_D2)&0xffffffffffffffff
    return mu.reg_read(UC_ARM_REG_S2)&0xffffffff
F32=[0,0x80000000,0x3f800000,0xbf800000,0x40000000,0x4f000000,0xcf000000,0x7f800000,0xff800000,
     0x7fc00000,0x00000001,0x007fffff,0x00800000,0x7f7fffff,0x40490fdb,0x4b000000,0x4effffff,0x47000000,0x40600000,0x402ccccd,0x40200000,0x3fc00000,0xc0600000,0xbfc00000,0x41200000,0x40e00000]
F64=[0,1<<63,0x3ff0000000000000,0xbff0000000000000,0x4000000000000000,0x41e0000000000000,
     0x7ff0000000000000,0x7ff8000000000000,0x0010000000000000,0x7fefffffffffffff,0x400921fb54442d18,0x4330000000000000]
INTS=[0,1,2,0x7fffffff,0x80000000,0xffffffff,0xfffffffe,100,0x12345678,1000000,0x40000000,0xdeadbeef]
vecs=[]
for name,enc,ind,outd in CONV:
    if name.startswith(("u32","i32")): inputs=INTS+[random.getrandbits(32) for _ in range(60)]
    elif name in ("f64_to_f32","f64_to_u32","f64_to_i32","f64_to_u32r","f64_to_i32r"): inputs=F64+[random.getrandbits(64) for _ in range(120)]
    else: inputs=F32+[random.getrandbits(32) for _ in range(120)]
    for a in inputs:
        r=run(enc,a,ind,outd)
        if r is None: continue
        vecs.append({"op":name,"a":hex(a),"r":hex(r)})
print(f"generated {len(vecs)} conversion vectors", file=sys.stderr)
json.dump({"oracle":"unicorn-2.1.4","fmt":"conv","vectors":vecs}, open(sys.argv[1] if len(sys.argv)>1 else '/tmp/conv.json','w'))
