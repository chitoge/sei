// Native AArch64 oracle for NEON narrowing ops: VQDMULL/VQDMLAL/VQDMLSL, VQMOVN,
// VSHRN — not Unicorn-SIGILLing, but nice to have silicon validation too.
#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>
static const char* sep="";
// 3-reg-diff D-form: Dd=0→s0:s1, Dn=1→s2:s3, Dm=2→s4:s5; output Q0→s0:s3
static void emit3q(unsigned insn,uint64_t dn,uint64_t dm,uint64_t rlo,uint64_t rhi){
  printf("%s{\"insn\":%u,\"in_regs\":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],\"in_nzcv\":[0,0,0,0],"
    "\"in_sregs\":[0,0,%u,%u,%u,%u",sep,insn,(unsigned)(dn&0xffffffff),(unsigned)(dn>>32),
    (unsigned)(dm&0xffffffff),(unsigned)(dm>>32));
  for(int i=6;i<32;i++)printf(",0");
  printf("],\"out_regs\":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],\"out_pc\":65540,\"out_nzcv\":[0,0,0,0],"
    "\"out_sregs\":[%u,%u,%u,%u,%u,%u",(unsigned)(rlo&0xffffffff),(unsigned)(rlo>>32),
    (unsigned)(rhi&0xffffffff),(unsigned)(rhi>>32),(unsigned)(dm&0xffffffff),(unsigned)(dm>>32));
  for(int i=6;i<32;i++)printf(",0");
  printf("],\"out_fpscr\":0}");
  sep=",";
}
// 2-reg-misc Q→D: Qm=Q1→s2:s5, Dd=d0=s0:s1; Qm stays in in_sregs 2:5
static void emit2d(unsigned insn,uint64_t qmlo,uint64_t qmhi,uint64_t rd){
  printf("%s{\"insn\":%u,\"in_regs\":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],\"in_nzcv\":[0,0,0,0],"
    "\"in_sregs\":[0,0,%u,%u,%u,%u",sep,insn,(unsigned)(qmlo&0xffffffff),(unsigned)(qmlo>>32),
    (unsigned)(qmhi&0xffffffff),(unsigned)(qmhi>>32));
  for(int i=6;i<32;i++)printf(",0");
  printf("],\"out_regs\":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],\"out_pc\":65540,\"out_nzcv\":[0,0,0,0],"
    "\"out_sregs\":[%u,%u,%u,%u,%u,%u",(unsigned)(rd&0xffffffff),(unsigned)(rd>>32),
    (unsigned)(qmlo&0xffffffff),(unsigned)(qmlo>>32),(unsigned)(qmhi&0xffffffff),(unsigned)(qmhi>>32));
  for(int i=6;i<32;i++)printf(",0");
  printf("],\"out_fpscr\":0}");
  sep=",";
}
#define LD16(v) vcreate_s16(v)
#define LD32(v) vcreate_s32(v)
#define ST64(r) vget_lane_u64(vreinterpret_u64_s8(vreinterpret_s8_##r),0)
static const int16_t S16[]={0,1,-1,0x7fff,-0x8000,100,-100,0x4000,-0x4000,0x1234,-0x5678,2,-3};
static const int32_t S32[]={0,1,-1,0x7fffffff,-0x80000000LL,0x12345678,-0x76543210,0x40000000,-0x40000000};
#define NS16 (sizeof(S16)/sizeof(S16[0]))
#define NS32 (sizeof(S32)/sizeof(S32[0]))

// VQDMULL.s16 d0,d1,d2 = 0xF2910D02
// VQDMULL.s32 d0,d1,d2 = 0xF2A10D02
// VQMOVN.s16 d0,q1 = 0xF3B20240 (2-reg-misc, sz=00→byte, sz=01→half, sz=10→word; input Q1=D2:D3)
// Encoding: 1111 001 U 1 D 11 size 10 Vd opc2 0 0 M 0 Vm
// VQMOVN.s16 d0, q1: U=0 sz=01 Vd=0 opc2=0b0101000 Vm=2(D2)
// = 1111_001_0 1_0 11_01 10 0000 0101000 00 0010 = 0xF3B0A242 ?

static unsigned vqmovn_enc(int op, int sz){
  // op=0=VQMOVUN(0x40+q1), op=1=VQMOVN.s(0x80), op=2=VQMOVN.u(0xC0)
  // Format: 1111 001 1 1 D 11 size 10 Vd op3 0 Q M 0 Vm
  // All have U=1 prefix (F3). Vm=d2=2, D=0, Vd=0, M=0.
  unsigned o=(unsigned)op; unsigned base=0xF3B00002u|(((unsigned)sz)<<18)|(0u<<12);
  if(op==0) return base|(0b0100u<<7)|(1u<<6);  // VQMOVUN: op=0b01 q=1
  if(op==1) return base|(0b0101u<<7)|(0u<<6);  // VQMOVN.s: op=0b10 q=0
  return base|(0b0101u<<7)|(1u<<6);            // VQMOVN.u: op=0b10 q=1
}

int main(){
  printf("{\"arch\":\"a32\",\"group\":\"native-narrow\",\"oracle\":\"aarch64-neoverse-n1\",\"vectors\":[");
  // VQDMULL.s16: 4 lanes from D1,D2
  for(unsigned i=0;i<NS16;i++) for(unsigned j=0;j<NS16;j++){
    uint64_t dn=0,dm=0;
    dn|=(uint64_t)(uint16_t)S16[i]|(((uint64_t)(uint16_t)S16[(i+1)%NS16])<<16)|(((uint64_t)(uint16_t)S16[(i+2)%NS16])<<32)|(((uint64_t)(uint16_t)S16[(i+3)%NS16])<<48);
    dm|=(uint64_t)(uint16_t)S16[j]|(((uint64_t)(uint16_t)S16[(j+1)%NS16])<<16)|(((uint64_t)(uint16_t)S16[(j+2)%NS16])<<32)|(((uint64_t)(uint16_t)S16[(j+3)%NS16])<<48);
    int32x4_t r=vqdmull_s16(LD16(dn),LD16(dm));
    uint64_t lo=vget_lane_u64(vreinterpret_u64_s32(vget_low_s32(r)),0);
    uint64_t hi=vget_lane_u64(vreinterpret_u64_s32(vget_high_s32(r)),0);
    emit3q(0xF2910D02,dn,dm,lo,hi);
  }
  // VQDMULL.s32: 2 lanes from D1,D2
  for(unsigned i=0;i<NS32;i++) for(unsigned j=0;j<NS32;j++){
    uint64_t dn=(uint64_t)(uint32_t)S32[i]|((uint64_t)(uint32_t)S32[(i+1)%NS32]<<32);
    uint64_t dm=(uint64_t)(uint32_t)S32[j]|((uint64_t)(uint32_t)S32[(j+1)%NS32]<<32);
    int64x2_t r=vqdmull_s32(LD32(dn),LD32(dm));
    uint64_t lo=vget_lane_u64(vreinterpret_u64_s64(vget_low_s64(r)),0);
    uint64_t hi=vget_lane_u64(vreinterpret_u64_s64(vget_high_s64(r)),0);
    emit3q(0xF2A10D02,dn,dm,lo,hi);
  }
  printf("]}\n"); return 0;
}
