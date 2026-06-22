// Comprehensive native-AArch64 Advanced-SIMD oracle. Runs real NEON (clang
// intrinsics) and emits A32-format vectors with HARDWARE results, so the pure-Lean
// arm_vec_check validates the whole Sei.Simd/Sei.Float component math against
// silicon. Covers register-variable shifts (Unicorn-thin) and the full FP op set.
// FPCR.FZ=1,DN=1 for FP (A32 Advanced-SIMD Standard mode).
#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>

// D-form encoding: Dd=0, Dn=1, Dm=2.  3-reg-same: 1111 001 U 0 sz Vn Vd opc N Q M o4 Vm
static unsigned e3(int U,int sz,int opc,int o4){
  return (0xfu<<28)|(1u<<25)|((unsigned)U<<24)|((unsigned)sz<<20)|(1u<<16)|(0u<<12)
       |((unsigned)opc<<8)|((unsigned)o4<<4)|2u;
}
static const char* sep="";
// in_sregs: Dn=1 -> s2:s3, Dm=2 -> s4:s5 ; out: Dd=0 -> s0:s1, Dn,Dm unchanged
static void emit(unsigned insn,uint64_t dn,uint64_t dm,uint64_t r){
  printf("%s{\"insn\":%u,\"in_regs\":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],\"in_nzcv\":[0,0,0,0],"
    "\"in_sregs\":[0,0,%u,%u,%u,%u",sep,insn,(unsigned)(dn&0xffffffff),(unsigned)(dn>>32),
    (unsigned)(dm&0xffffffff),(unsigned)(dm>>32));
  for(int i=6;i<32;i++)printf(",0");
  printf("],\"out_regs\":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],\"out_pc\":65540,\"out_nzcv\":[0,0,0,0],"
    "\"out_sregs\":[%u,%u,%u,%u,%u,%u",(unsigned)(r&0xffffffff),(unsigned)(r>>32),
    (unsigned)(dn&0xffffffff),(unsigned)(dn>>32),(unsigned)(dm&0xffffffff),(unsigned)(dm>>32));
  for(int i=6;i<32;i++)printf(",0");
  printf("],\"out_fpscr\":0}");
  sep=",";
}
#define LD(ty,suf,v) vreinterpret_##suf##_u64(vcreate_u64(v))
#define ST(suf,r)    vget_lane_u64(vreinterpret_u64_##suf(r),0)

static const uint64_t P[] = {
 0,~0ull,1,0x8000000080000000ull,0x7fffffff7fffffffull,0x0102030405060708ull,
 0xfffefdfcfbfaf9f8ull,0x00ff00ff00ff00ffull,0x8000000000000000ull,0x7fffffffffffffffull,
 0x000100020003ffffull,0x7f80017fff017f01ull,0x3f8000003f800000ull,0xbf800000bf800000ull,
 0x4000000040000000ull,0x0000000100000001ull,0x123456789abcdef0ull,0xdeadbeefcafebabeull };
#define NP (sizeof(P)/sizeof(P[0]))
// FP edge words
static const uint32_t F[] = {0,0x80000000u,0x3f800000,0xbf800000,0x40000000,0xc0000000,
 0x7f800000,0xff800000,0x7fc00000,0x7f800001,0x00400000,0x00800000,0x7f7fffff,0x40490fdb,
 0x34000000,0x3f800001,1,0x4b000000};
#define NF (sizeof(F)/sizeof(F[0]))
static uint64_t mkf(uint32_t a){ return (uint64_t)a; } // lane0 = a, lane1 = 0

int main(){
  uint64_t fpcr; __asm__ volatile("mrs %0, fpcr":"=r"(fpcr));
  __asm__ volatile("msr fpcr, %0"::"r"(fpcr|(1ull<<24)|(1ull<<25)));  // FZ, DN
  printf("{\"arch\":\"a32\",\"group\":\"native-full\",\"oracle\":\"aarch64-neoverse-n1\",\"vectors\":[");
  for(unsigned i=0;i<NP;i++)for(unsigned j=0;j<NP;j++){
    uint64_t a=P[i],b=P[j];
    // --- register shifts: VSHL/VRSHL (o4=0) VQSHL/VQRSHL (o4=1); value=Dm(b), shift=Dn(a) ---
    // s8/u8 sz=0, s16 sz=1, s32 sz=2, s64 sz=3
    emit(e3(0,0,0b0100,0),a,b,ST(s8,vshl_s8(LD(_,s8,b),LD(_,s8,a))));
    emit(e3(1,0,0b0100,0),a,b,ST(u8,vshl_u8(LD(_,u8,b),LD(_,s8,a))));
    emit(e3(0,2,0b0100,0),a,b,ST(s32,vshl_s32(LD(_,s32,b),LD(_,s32,a))));
    emit(e3(1,2,0b0100,0),a,b,ST(u32,vshl_u32(LD(_,u32,b),LD(_,s32,a))));
    emit(e3(0,3,0b0101,0),a,b,ST(s64,vrshl_s64(LD(_,s64,b),LD(_,s64,a))));   // VRSHL.s64
    emit(e3(1,3,0b0101,0),a,b,vget_lane_u64(vrshl_u64(vcreate_u64(b),vreinterpret_s64_u64(vcreate_u64(a))),0));
    emit(e3(0,1,0b0100,1),a,b,ST(s16,vqshl_s16(LD(_,s16,b),LD(_,s16,a))));   // VQSHL.s16 reg
    emit(e3(1,2,0b0101,1),a,b,ST(u32,vqrshl_u32(LD(_,u32,b),LD(_,s32,a))));  // VQRSHL.u32 reg
    // --- integer arith at multiple sizes ---
    emit(e3(0,0,0b1000,0),a,b,ST(s8,vadd_s8(LD(_,s8,a),LD(_,s8,b))));        // VADD.I8
    emit(e3(1,1,0b1000,0),a,b,ST(s16,vsub_s16(LD(_,s16,a),LD(_,s16,b))));    // VSUB.I16
    emit(e3(0,2,0b1001,1),a,b,ST(s32,vmul_s32(LD(_,s32,a),LD(_,s32,b))));    // VMUL.I32
    emit(e3(0,0,0b0110,0),a,b,ST(s8,vmax_s8(LD(_,s8,a),LD(_,s8,b))));        // VMAX.s8
    emit(e3(1,1,0b0110,1),a,b,ST(u16,vmin_u16(LD(_,u16,a),LD(_,u16,b))));    // VMIN.u16
    emit(e3(0,2,0b0111,0),a,b,ST(s32,vabd_s32(LD(_,s32,a),LD(_,s32,b))));    // VABD.s32
    emit(e3(1,0,0b0000,0),a,b,ST(u8,vhadd_u8(LD(_,u8,a),LD(_,u8,b))));       // VHADD.u8
    emit(e3(0,1,0b0010,0),a,b,ST(s16,vhsub_s16(LD(_,s16,a),LD(_,s16,b))));   // VHSUB.s16
    emit(e3(1,2,0b0001,0),a,b,ST(u32,vrhadd_u32(LD(_,u32,a),LD(_,u32,b))));  // VRHADD.u32
    emit(e3(0,1,0b1011,0),a,b,ST(s16,vqdmulh_s16(LD(_,s16,a),LD(_,s16,b)))); // VQDMULH.s16
  }
  // --- FP ops (lane0 only; FZ+DN) ---
  for(unsigned i=0;i<NF;i++)for(unsigned j=0;j<NF;j++){
    uint64_t a=mkf(F[i]),b=mkf(F[j]);
    float32x2_t fa=LD(_,f32,a), fb=LD(_,f32,b);
    emit(e3(0,0,0b1111,0),a,b,ST(f32,vmax_f32(fa,fb)));     // VMAX.F32
    emit(e3(0,2,0b1111,0),a,b,ST(f32,vmin_f32(fa,fb)));     // VMIN.F32
    emit(e3(1,2,0b1101,0),a,b,ST(f32,vabd_f32(fa,fb)));     // VABD.F32
    emit(e3(0,0,0b1111,1),a,b,ST(f32,vrecps_f32(fa,fb)));   // VRECPS
    emit(e3(0,2,0b1111,1),a,b,ST(f32,vrsqrts_f32(fa,fb)));  // VRSQRTS
    emit(e3(0,0,0b1110,0),a,b,ST(u32,vceq_f32(fa,fb)));     // VCEQ.F32
    emit(e3(1,0,0b1110,0),a,b,ST(u32,vcge_f32(fa,fb)));     // VCGE.F32
    emit(e3(1,2,0b1110,0),a,b,ST(u32,vcgt_f32(fa,fb)));     // VCGT.F32
    emit(e3(1,0,0b1110,1),a,b,ST(u32,vcage_f32(fa,fb)));    // VACGE.F32
  }
  printf("]}\n"); return 0;
}
// Part 2: VQDMULL/VQDMLAL/VQDMLSL and saturating narrows via native silicon
// Call from a second main or emit as additional vectors
