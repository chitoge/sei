// Native AArch64 NEON-FP oracle under Standard mode (FPCR.FZ=1,DN=1) — matches A32
// Advanced SIMD FP. Validates Sei.Simd vfAdd/vfSub/vfMul against REAL silicon,
// including subnormal-flush / default-NaN / saturation lanes Unicorn hits only randomly.
#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>
static const uint32_t E[] = {0,0x80000000u,0x3f800000,0xbf800000,0x40000000,0xc0000000,
  0x7f800000,0xff800000,0x7fc00000,0x7f800001,0xffc00000,1,0x80000001u,0x007fffff,0x00800000,
  0x7f7fffff,0xff7fffff,0x40490fdb,0x00400000,0x34000000,0x4b7fffff,0x3f800001};
#define N (sizeof(E)/sizeof(E[0]))
static void setfpcr(){ uint64_t v; __asm__ volatile("mrs %0, fpcr":"=r"(v));
  v |= (1ull<<24)|(1ull<<25); __asm__ volatile("msr fpcr, %0"::"r"(v)); }  // FZ(24) DN(25)
static void emit(const char*sep,unsigned insn,uint32_t a,uint32_t b,uint32_t r){
  // VADD/VSUB/VMUL.F32 d0,d1,d2 : D1 lane0=a(s2) D2 lane0=b(s4) D0 lane0=r(s0)
  printf("%s{\"insn\":%u,\"in_regs\":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],\"in_nzcv\":[0,0,0,0],"
    "\"in_sregs\":[0,0,%u,0,%u,0",sep,insn,a,b);
  for(int i=6;i<32;i++)printf(",0");
  printf("],\"out_regs\":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],\"out_pc\":65540,\"out_nzcv\":[0,0,0,0],"
    "\"out_sregs\":[%u,0,%u,0,%u,0",r,a,b);
  for(int i=6;i<32;i++)printf(",0");
  printf("],\"out_fpscr\":0}");
}
int main(){
  setfpcr();
  printf("{\"arch\":\"a32\",\"group\":\"native-fp\",\"oracle\":\"aarch64-neoverse-n1-stdfp\",\"vectors\":[");
  const char*sep="";
  for(unsigned i=0;i<N;i++)for(unsigned j=0;j<N;j++){
    float32x2_t a=vdup_n_f32(0),b=vdup_n_f32(0);
    a=vset_lane_f32(*(float*)&E[i],a,0); b=vset_lane_f32(*(float*)&E[j],b,0);
    uint32_t add=vget_lane_u32(vreinterpret_u32_f32(vadd_f32(a,b)),0);
    uint32_t sub=vget_lane_u32(vreinterpret_u32_f32(vsub_f32(a,b)),0);
    uint32_t mul=vget_lane_u32(vreinterpret_u32_f32(vmul_f32(a,b)),0);
    emit(sep,0xF2010D02,E[i],E[j],add);sep=",";   // VADD.F32 d0,d1,d2
    emit(sep,0xF2210D02,E[i],E[j],sub);            // VSUB.F32
    emit(sep,0xF3010D12,E[i],E[j],mul);            // VMUL.F32
  }
  printf("]}\n");return 0;
}
