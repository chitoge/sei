// Native AArch64 Advanced SIMD oracle: compute NEON lane semantics on REAL silicon,
// emit A32-format vectors (the .64 saturating ops Unicorn's JIT SIGILLs on).
#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>
static const int64_t E[] = {0,1,-1,2,-2,0x7fffffffffffffffLL,(int64_t)0x8000000000000000ULL,
  0x7ffffffffffffffeLL,(int64_t)0x8000000000000001ULL,100,-100,0x123456789abcdefLL,
  (int64_t)0xfedcba9876543210ULL,(int64_t)0x4000000000000000ULL,(int64_t)0xc000000000000000ULL};
#define N (sizeof(E)/sizeof(E[0]))
static void emit(const char* sep,unsigned insn,uint64_t a,uint64_t b,uint64_t r){
  // VQADD/VQSUB.s64 D0,D1,D2 : D1=a(s2,s3) D2=b(s4,s5) D0=r(s0,s1)
  printf("%s{\"insn\":%u,\"in_regs\":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],\"in_nzcv\":[0,0,0,0],"
    "\"in_sregs\":[0,0,%u,%u,%u,%u",sep,insn,(unsigned)(a&0xffffffff),(unsigned)(a>>32),(unsigned)(b&0xffffffff),(unsigned)(b>>32));
  for(int i=6;i<32;i++)printf(",0");
  printf("],\"out_regs\":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],\"out_pc\":65540,\"out_nzcv\":[0,0,0,0],"
    "\"out_sregs\":[%u,%u,%u,%u,%u,%u",(unsigned)(r&0xffffffff),(unsigned)(r>>32),
    (unsigned)(a&0xffffffff),(unsigned)(a>>32),(unsigned)(b&0xffffffff),(unsigned)(b>>32));
  for(int i=6;i<32;i++)printf(",0");
  printf("],\"out_fpscr\":0}");
}
int main(){
  printf("{\"arch\":\"a32\",\"group\":\"native-silicon\",\"oracle\":\"aarch64-neoverse-n1\",\"vectors\":[");
  const char* sep="";
  for(unsigned i=0;i<N;i++)for(unsigned j=0;j<N;j++){
    int64x1_t a=vcreate_s64(E[i]), b=vcreate_s64(E[j]);
    uint64_t qadd=vget_lane_u64(vreinterpret_u64_s64(vqadd_s64(a,b)),0);   // VQADD.s64
    uint64_t qsub=vget_lane_u64(vreinterpret_u64_s64(vqsub_s64(a,b)),0);   // VQSUB.s64
    emit(sep,0xF2310012,E[i],E[j],qadd); sep=",";   // VQADD.s64 D0,D1,D2
    emit(sep,0xF2310212,E[i],E[j],qsub);            // VQSUB.s64 D0,D1,D2
  }
  // unsigned .64 too: VQADD.u64 = 0xF3310012
  for(unsigned i=0;i<N;i++)for(unsigned j=0;j<N;j++){
    uint64x1_t a=vcreate_u64(E[i]),b=vcreate_u64(E[j]);
    uint64_t r=vget_lane_u64(vqadd_u64(a,b),0);
    emit(sep,0xF3310012,E[i],E[j],r);
  }
  printf("]}\n"); return 0;
}
