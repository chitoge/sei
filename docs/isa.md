# ISA coverage

SEI implements ARM and MIPS instructions as pure Lean functions. Every
instruction group listed here is covered by **Unicorn-generated test vectors**:
a Python oracle runs the same instruction on real hardware via Unicorn, captures
the output, and SEI replays those vectors byte-for-byte in its test suite. If
SEI and Unicorn disagree, the test fails.

The test corpora live in `tests/` and are committed to the repo. The oracle
scripts that generated them are in `tools/`.

---

## ARM A32

Classic (non-Cortex-M) 32-bit ARM. This is the mode that most legacy firmware
and bootloaders use.

| Group | What's covered |
|-------|---------------|
| Data-processing | MOV, MVN, AND, ORR, EOR, BIC, ADD, SUB, RSB, ADC, SBC, RSC, CMP, CMN, TST, TEQ — all with immediate (rotated), shifted-register, and register forms |
| Wide immediate | MOVW, MOVT — 16-bit halves of a 32-bit load |
| Multiply | MUL, MLA, UMULL, UMLAL, SMULL, SMLAL |
| Load / store | LDR, STR, LDRB, STRB, LDRH, STRH, LDRD, STRD — immediate and register with all writeback modes |
| Block transfer | LDM, STM — all four addressing modes (IA, IB, DA, DB), user-bank `^` form |
| Exclusive access | LDREX, STREX — exclusive monitor modelled |
| Branches | B, BL, BX, BLX — including interworking and branch-exchange |
| Coprocessor | MCR, MRC (CP15) — logged as typed `cp15` effects |
| Exceptions | SVC, BKPT; exception entry and return for UND, SWI, PABT, DABT, IRQ, FIQ; SPSR save/restore; high-vector mode |
| Saturation | SSAT, USAT, QADD, QSUB, QDADD, QDSUB |

Test corpus: `tests/armvec/a32-dp-vectors.json`, `a32-branch-vectors.json`,
`a32-ldm-vectors.json` — 1132+ vectors total.

## ARM Thumb (T16 / T32)

SEI supports 16-bit Thumb (T16) and the 32-bit Thumb-2 extension (T32).

| Format | What's covered |
|--------|---------------|
| T16 | ALU (ADD, SUB, MOV, CMP, AND, ORR, …), branches (B, BL, BX, CBZ, CBNZ), load/store (LDR/STR imm and reg), push/pop |
| T32 | LDM, STM; 32-bit instruction dispatch (the T32 prefix decode) |

The CPU starts in Thumb state when `cpu.arch` is `"thumb"` or
`entry.exception_state` is `"thumb"`.

## VFP (f16 / f32 / f64)

SEI's floating-point is a standalone IEEE-754 soft-float implementation —
not a wrapper around the host FPU — so results are bit-exact across platforms.

| Group | What's covered |
|-------|---------------|
| Arithmetic | VADD, VSUB, VMUL, VDIV, VNMUL, VNMLA, VNMLS |
| Fused multiply | VFMA, VFMS, VFNMA, VFNMS |
| Conversion | VCVT between int↔fp, f16↔f32, f32↔f64; VCVTR (round-to-nearest) |
| Compare | VCMP, VCMPE (with and without NaN trap) |
| Move | VMOV (immediate, register, scalar) |
| Load / store | VLDR, VSTR (single), VLDM, VSTM (multiple, IA and DB) |

Rounding modes, subnormals, infinities, and NaNs are all tested.

Test corpora: `tests/float/binary32-vectors.json`, `binary64-vectors.json`,
`fma-vectors.json`, `conv-vectors.json`.

## NEON / Advanced SIMD

NEON operates on 64-bit D-registers and 128-bit Q-registers (pairs of D).
Results are bit-exact against Unicorn.

| Group | What's covered |
|-------|---------------|
| Bitwise | VAND, VORR, VEOR, VBIC, VORN, VBSL, VMVN |
| Integer arithmetic | VADD, VSUB, VQADD, VQSUB, VHADD, VHSUB, VRHADD, VABA, VABAL, VABD, VABDL |
| Multiply | VMUL, VMLA, VMLS, VMULL, VMLAL, VMLSL, VQDMULH, VQRDMULH |
| Compare | VCEQ, VCGE, VCGT, VCLE, VCLT, VCGT, VTST |
| Shift | VSHL, VSHR, VRSHL, VRSHR, VQSHL, VQSHRN, VRSHRN |
| Float arithmetic | VADD, VSUB, VMUL, VMLA, VMLS, VABD, VABS, VNEG, VCVT (int↔float) |
| Immediate | VMOV (immediate), VMVN (immediate), VORR (immediate) |

All lane widths (8, 16, 32, 64 bit) are covered where the instruction supports them.

---

## MIPS32r2

32-bit MIPS little-endian, targeting MIPS32r2 as implemented by common embedded SoCs.

| Group | What's covered |
|-------|---------------|
| ALU register | ADDU, SUBU, AND, OR, XOR, NOR, SLL, SRL, SRA, SLLV, SRLV, SRAV, SLT, SLTU, ROTR, ROTRV |
| ALU immediate | ADDIU, ANDI, ORI, XORI, SLTI, SLTIU, LUI |
| Multiply / divide | MULT, MULTU, DIV, DIVU, MFHI, MFLO, MTHI, MTLO |
| SPECIAL2 | MUL (three-register), CLZ, CLO |
| SPECIAL3 | EXT (bit-field extract), INS (bit-field insert) |
| Branch | BEQ, BNE, BGTZ, BLEZ, BGEZ, BLTZ, BGEZAL, BLTZAL — all with branch-delay slots; MOVCI (FP-conditional move) |
| Load / store | LW, SW, LB, SB, LH, SH, LBU, LHU, LWL, LWR, SWL, SWR |
| Jump | J, JAL, JR, JALR, JALX (mode-switch to MIPS16e) |
| CP0 | MFC0, MTC0 — Status, Cause, EPC, Count, Compare, BadVAddr, Index, EntryHi, EntryLo, Context |
| FP (COP1) | MFC1, MTC1, MFHC1, MTHC1; COP1X indexed FP loads/stores and FP-MAC |
| TLB | TLBWI, TLBWR, TLBR, TLBP |

CP0 Count/Compare drives a timer interrupt: when Count reaches Compare, an IP7
interrupt fires if the interrupt enable bits allow it. The TLB supports kseg0,
kseg1 (unmapped), and a software-managed TLB for mapped segments.

Test corpus: `tests/mipsvec/mips32-vectors.json` — 1939 Unicorn-validated vectors.

## MIPS16e

MIPS16e is a 16-bit compressed ISA that the MIPS32r2 core switches into via
JALX. Instructions are 16 bits wide (some extended to 32 bits with the EXTEND
prefix). There are no branch-delay slots in MIPS16e.

SEI implements a complete MIPS16e decoder (`step16` / `execute16`). When the
program counter has bit 0 set, SEI automatically runs in MIPS16e mode; when bit 0
is clear, it's in MIPS32 mode. No separate mode register is needed.

| Group | What's covered |
|-------|---------------|
| ALU | ADDIU, ADDIU.SP, ADDIU.PC, SLTI, SLTIU, CMPI (T-register compare) |
| Three-register | ADDU, SUBU (RRR format) |
| Register-register | SLT, SLTU, SLLV, SRLV, SRAV, NEG, AND, OR, XOR, NOT, MULT, MULTU, DIV, DIVU, MFHI, MFLO |
| Shift | SLL, SRL, SRA (immediate shift count) |
| Load | LB, LBU, LH, LHU, LW, LWSP (stack-relative), LWPC (PC-relative) |
| Store | SB, SH, SW, SWSP (stack-relative) |
| Branch | B (unconditional), BEQZ, BNEZ, BTEQZ, BTNEZ (T-register branches) |
| Jump | JR, JRC, JALRC, JAL (2-word), JALX (2-word, switches back to MIPS32) |
| Stack frame | SAVE, RESTORE (prologue/epilogue macros) |
| Immediate extension | EXTEND prefix — extends the immediate field of the following instruction to 16 bits |
| Register moves | MOV32R, MOVR32 — move between MIPS16e and MIPS32 register spaces |
| I8 ops | ADJSP, SWRASP, BTEQZ, BTNEZ |

MIPS16e and MIPS32 can call each other freely: JALX in MIPS32 jumps to a
MIPS16e target; JAL/JALX in MIPS16e can jump back to MIPS32.

---

## What's not covered yet

- **Cortex-M** (NVIC, SysTick, MPU, stack-banked exception entry) — the T16/T32
  subset runs, but the Cortex-M-specific system registers and exception model
  are not implemented.
- **Full T32** — 32-bit Thumb-2 beyond LDM/STM (e.g. IT blocks, saturating
  arithmetic, DSP extensions).
- **RISC-V** — deferred; no decoder exists yet.
- **MIPS DSP / MSA** — extended MIPS SIMD is not implemented.

If you hit an unimplemented instruction, the run stops with
`stop=unsupportedInstr` and the report lists the PC, opcode, and a mnemonic
hint for each one.
