/-
Classic (non-Cortex-M) ARM A32 slice over the SEI Lean core — pure, total, typed
effects. Sufficient for the reset slice (E02) and exception entry/return (E03):
MOV/MVN/ADD/SUB/CMP/ORR/AND (rotated imm), MOVW/MOVT, LDR/STR imm, B/BL, MCR/MRC
(CP15, logged as effects), SVC, undefined-instruction + exception path.

`pc` is the instruction address; reads of r15 yield `pc + 8` (classic pipeline).
Register banking is simplified (one register file; the return address is written
to r14 on exception entry), matching the Python reference.
-/
import Sei.Core
import Sei.Float
import Sei.Simd
open Sei.Core

namespace Sei.Isa.Arm

def MODE_USR : Nat := 0x10
def MODE_FIQ : Nat := 0x11
def MODE_IRQ : Nat := 0x12
def MODE_SVC : Nat := 0x13
def MODE_ABT : Nat := 0x17
def MODE_UND : Nat := 0x1B

/-- vector offset and entry mode for each exception kind. -/
def vectorInfo : String → (Nat × Nat)
  | "undef" => (0x04, MODE_UND)
  | "swi"   => (0x08, MODE_SVC)
  | "pabt"  => (0x0C, MODE_ABT)
  | "dabt"  => (0x10, MODE_ABT)
  | "irq"   => (0x18, MODE_IRQ)
  | "fiq"   => (0x1C, MODE_FIQ)
  | _       => (0x00, MODE_SVC)

structure Cpu where
  regs : Array Word := (List.replicate 16 (0 : Word)).toArray  -- r0..r14 (+ r15 unused)
  pc : Word := 0
  n : Bool := false
  z : Bool := false
  c : Bool := false
  v : Bool := false
  mode : Nat := MODE_SVC
  iMask : Bool := true
  fMask : Bool := true
  tbit : Bool := false                       -- CPSR T (Thumb) bit
  itState : Nat := 0                         -- CPSR IT[7:0]: {firstcond[3:0], mask[3:0]}
  highVectors : Bool := false
  haltOnSelfBranch : Bool := true
  spsr : List (Nat × Word) := []            -- saved CPSR per mode
  banked : List ((Nat × Nat) × Word) := []  -- banked r13/r14 per mode ((mode,reg)→val)
  cp15 : List ((Nat × Nat × Nat × Nat) × Word) := [((0,0,0,0), 0x41069265)]  -- MIDR
  vreg : Array (BitVec 64) := (List.replicate 32 (0 : BitVec 64)).toArray   -- VFP D0..D31
  fpscr : Word := 0                          -- VFP status/control (NZCV from VCMP)
  fpexc : Word := 0x40000000                 -- VFP exception/enable register (EN bit set)
  irqPending : Bool := false
  fiqPending : Bool := false
  halted : Bool := false
  blocked : Bool := false
  exclReserved : Bool := false   -- exclusive access monitor (set by LDREX, cleared by STREX)
  deriving Inhabited

abbrev St := Cpu × Machine

/-- r15 reads as pc+8. -/
def Cpu.rRead (c : Cpu) (i : Nat) : Word := if i == 15 then c.pc + 8 else c.regs.getD i 0
def Cpu.setR (c : Cpu) (i : Nat) (v : Word) : Cpu :=
  if i == 15 then { c with pc := v } else { c with regs := c.regs.setIfInBounds i v }

/-! VFP register file: D0..D31 (64-bit). S[n] is a 32-bit half of D[n/2] (n<32). -/
def Cpu.dReg (c : Cpu) (n : Nat) : BitVec 64 := c.vreg.getD n 0
def Cpu.setDReg (c : Cpu) (n : Nat) (v : BitVec 64) : Cpu := { c with vreg := c.vreg.setIfInBounds n v }
-- Q registers (128-bit) overlay register pairs D2n:D2n+1 (n is the Q index)
def Cpu.qReg (c : Cpu) (n : Nat) : Nat := (c.dReg (2*n+1)).toNat * 18446744073709551616 + (c.dReg (2*n)).toNat
def Cpu.setQReg (c : Cpu) (n : Nat) (v : Nat) : Cpu :=
  (c.setDReg (2*n) (BitVec.ofNat 64 (v % 18446744073709551616))).setDReg (2*n+1) (BitVec.ofNat 64 (v / 18446744073709551616))
def Cpu.sReg (c : Cpu) (n : Nat) : Word :=
  let d := (c.vreg.getD (n / 2) 0).toNat
  BitVec.ofNat 32 (if n % 2 == 0 then d % 4294967296 else d / 4294967296)
def Cpu.setSReg (c : Cpu) (n : Nat) (v : Word) : Cpu :=
  let d := (c.vreg.getD (n / 2) 0).toNat
  let lo := d % 4294967296; let hi := d / 4294967296
  let d' := if n % 2 == 0 then hi * 4294967296 + v.toNat else v.toNat * 4294967296 + lo
  { c with vreg := c.vreg.setIfInBounds (n / 2) (BitVec.ofNat 64 d') }

def Cpu.getBank (c : Cpu) (mode reg : Nat) : Word :=
  (c.banked.find? (·.1 == (mode, reg))).map (·.2) |>.getD 0
def Cpu.setBank (c : Cpu) (mode reg : Nat) (v : Word) : Cpu :=
  { c with banked := ((mode, reg), v) :: c.banked.filter (·.1 != (mode, reg)) }

/-- Switch processor mode, banking r13 (SP) and r14 (LR): the outgoing mode's
    SP/LR are saved and the incoming mode's are restored (B4: real banked regs). -/
def Cpu.switchMode (c : Cpu) (newMode : Nat) : Cpu :=
  if newMode == c.mode then c
  else
    let c := (c.setBank c.mode 13 (c.regs.getD 13 0)).setBank c.mode 14 (c.regs.getD 14 0)
    let regs := (c.regs.setIfInBounds 13 (c.getBank newMode 13)).setIfInBounds 14 (c.getBank newMode 14)
    { c with regs := regs, mode := newMode }

def packCpsr (c : Cpu) : Word :=
  BitVec.ofNat 32 (c.mode ||| (if c.tbit then 1 <<< 5 else 0) ||| (if c.fMask then 1 <<< 6 else 0) ||| (if c.iMask then 1 <<< 7 else 0) |||
    (if c.v then 1 <<< 28 else 0) ||| (if c.c then 1 <<< 29 else 0) |||
    (if c.z then 1 <<< 30 else 0) ||| (if c.n then 1 <<< 31 else 0))

def unpackCpsr (c : Cpu) (s : Word) : Cpu :=
  let w := s.toNat
  let c := c.switchMode (w &&& 0x1f)      -- restore mode + bank-swap r13/r14
  { c with tbit := (w >>> 5) &&& 1 == 1, fMask := (w >>> 6) &&& 1 == 1, iMask := (w >>> 7) &&& 1 == 1,
           v := (w >>> 28) &&& 1 == 1, c := (w >>> 29) &&& 1 == 1,
           z := (w >>> 30) &&& 1 == 1, n := (w >>> 31) &&& 1 == 1 }

def cp15Get (c : Cpu) (k : Nat × Nat × Nat × Nat) : Word :=
  (c.cp15.find? (·.1 == k)).map (·.2) |>.getD 0
def cp15Set (c : Cpu) (k : Nat × Nat × Nat × Nat) (v : Word) : Cpu :=
  { c with cp15 := (k, v) :: c.cp15.filter (·.1 != k) }
def spsrGet (c : Cpu) (mode : Nat) : Word :=
  (c.spsr.find? (·.1 == mode)).map (·.2) |>.getD 0
def spsrSet (c : Cpu) (mode : Nat) (v : Word) : Cpu :=
  { c with spsr := (mode, v) :: c.spsr.filter (·.1 != mode) }

/-- ARMv7 short-descriptor VA→PA translation via TTBR0/TTBR1.
    When SCTLR.M=0 (MMU off), VA = PA. Page-table walks read physical memory. -/
-- Page-table walks use direct memRead (no device dispatch, no trace events).
def Cpu.translateArm (c : Cpu) (m : Machine) (va : Nat) : Option Nat × Machine :=
  let sctlr := (cp15Get c (1, 0, 0, 0)).toNat
  if sctlr &&& 1 == 0 then (some va, m)  -- MMU disabled: VA = PA
  else
    let ttbcr    := (cp15Get c (2, 0, 0, 2)).toNat
    let n        := ttbcr &&& 7
    let ttbr     := if n == 0 || va >>> (32 - n) == 0
                    then (cp15Get c (2, 0, 0, 0)).toNat
                    else (cp15Get c (2, 0, 0, 1)).toNat
    let baseBits := 14 - n
    let l1Base   := (ttbr >>> baseBits) <<< baseBits
    let l1Idx    := (va &&& 0xFFFFFFFF) >>> 20
    let l1Addr   := BitVec.ofNat 32 (l1Base + l1Idx * 4)
    match Sei.Core.memRead m.regions l1Addr 32 with
    | .error _ => (none, m)
    | .ok desc =>
      let d := desc.toNat
      match d &&& 3 with
      | 0 => (none, m)
      | 2 =>
        if d &&& (1 <<< 18) != 0 then
          (some ((d &&& 0xFF000000) ||| (va &&& 0x00FFFFFF)), m)  -- Supersection (16 MB)
        else
          (some ((d &&& 0xFFF00000) ||| (va &&& 0x000FFFFF)), m)  -- Section (1 MB)
      | 1 =>
        let l2Base := (d >>> 10) <<< 10
        let l2Idx  := (va >>> 12) &&& 0xFF
        let l2Addr := BitVec.ofNat 32 (l2Base + l2Idx * 4)
        match Sei.Core.memRead m.regions l2Addr 32 with
        | .error _ => (none, m)
        | .ok desc2 =>
          let d2 := desc2.toNat
          match d2 &&& 3 with
          | 0 => (none, m)
          | 1 => (some ((d2 &&& 0xFFFF0000) ||| (va &&& 0xFFFF)), m)  -- Large page (64 KB)
          | _ => (some ((d2 &&& 0xFFFFF000) ||| (va &&& 0xFFF)), m)   -- Small page (4 KB)
      | _ => (none, m)

/-- MMU-aware memory read: translate VA→PA, then busRead. -/
def Cpu.memRead (c : Cpu) (m : Machine) (va : Word) (width : Nat)
    (fetch : Bool := false) : Except Fault Word × Machine :=
  match c.translateArm m va.toNat with
  | (none, m)    => (.error .perm, m)
  | (some pa, m) => m.busRead (BitVec.ofNat 32 pa) width (fetch := fetch)

/-- MMU-aware memory write: translate VA→PA, then busWrite. -/
def Cpu.memWrite (c : Cpu) (m : Machine) (va : Word) (v : Word) (width : Nat)
    : Except Fault Unit × Machine :=
  match c.translateArm m va.toNat with
  | (none, m)    => (.error .perm, m)
  | (some pa, m) => m.busWrite (BitVec.ofNat 32 pa) v width

/-- Enter an exception vector: bank LR/SPSR, switch mode, mask, emit effect. -/
def takeException (c : Cpu) (m : Machine) (kind : String) (ret : Word) : Cpu × Machine :=
  let (off, newMode) := vectorInfo kind
  let base : Word := if c.highVectors then 0xFFFF0000 else 0
  let target := base + BitVec.ofNat 32 off
  let spsr := packCpsr c
  let c := (spsrSet c newMode spsr)
  let c := c.switchMode newMode                              -- bank r13/r14 of both modes
  let c := { c with regs := c.regs.setIfInBounds 14 ret }    -- new mode's LR = return addr
  let c := { c with iMask := true, fMask := (kind == "fiq") || c.fMask }
  let m := m.emit (.exception kind target newMode)
  ({ c with pc := target, tbit := false }, m)

-- Full ARM condition-code table (A8.3). Previously only EQ/NE/GE/LT were
-- modeled and everything else fell through to "always" — which silently turned
-- CS/CC/MI/PL/VS/VC/HI/LS/GT/LE into unconditional execution.
def condHolds (c : Cpu) (cc : Nat) : Bool :=
  match cc with
  | 0x0 => c.z                      -- EQ
  | 0x1 => !c.z                     -- NE
  | 0x2 => c.c                      -- CS/HS
  | 0x3 => !c.c                     -- CC/LO
  | 0x4 => c.n                      -- MI
  | 0x5 => !c.n                     -- PL
  | 0x6 => c.v                      -- VS
  | 0x7 => !c.v                     -- VC
  | 0x8 => c.c && !c.z              -- HI
  | 0x9 => !c.c || c.z              -- LS
  | 0xA => c.n == c.v               -- GE
  | 0xB => c.n != c.v               -- LT
  | 0xC => !c.z && (c.n == c.v)     -- GT
  | 0xD => c.z || (c.n != c.v)      -- LE
  | _   => true                     -- AL (0xE); 0xF handled as unconditional

def setNZ (c : Cpu) (r : Word) : Cpu := { c with n := (r >>> 31) &&& 1 == 1, z := r == 0 }

-- NZCV from an addition/subtraction (carry + signed overflow).
def setAddFlags (c : Cpu) (a b r : Word) : Cpu :=
  { c with n := (r >>> 31) &&& 1 == 1, z := r == 0,
           c := a.toNat + b.toNat ≥ 2 ^ 32,
           v := ((a >>> 31) &&& 1 == (b >>> 31) &&& 1) && ((r >>> 31) &&& 1 != (a >>> 31) &&& 1) }
def setSubFlags (c : Cpu) (a b r : Word) : Cpu :=
  { c with n := (r >>> 31) &&& 1 == 1, z := r == 0,
           c := a.toNat ≥ b.toNat,
           v := ((a >>> 31) &&& 1 != (b >>> 31) &&& 1) && ((r >>> 31) &&& 1 != (a >>> 31) &&& 1) }

def bit (x : Word) (i : Nat) : Bool := (x >>> i) &&& 1 == 1

/-- ARM `AddWithCarry` (A2.2.1): returns (result, carry-out, signed-overflow). -/
def addWithCarry (a b : Word) (cin : Bool) : Word × Bool × Bool :=
  let ci := if cin then 1 else 0
  let usum := a.toNat + b.toNat + ci
  let r : Word := BitVec.ofNat 32 usum
  let ssum := a.toInt + b.toInt + (ci : Int)
  (r, usum ≥ 2 ^ 32, r.toInt != ssum)

/-- Shifter operand for an immediate shift amount `imm5` (A5.1.1): value + carry-out. -/
def immShift (rm : Word) (stype imm5 : Nat) (cin : Bool) : Word × Bool :=
  match stype with
  | 0 => if imm5 == 0 then (rm, cin) else (rm <<< imm5, bit rm (32 - imm5))           -- LSL
  | 1 => let n := if imm5 == 0 then 32 else imm5                                       -- LSR (#0 ⇒ 32)
         (if n == 32 then 0 else rm >>> n, bit rm (n - 1))
  | 2 => let n := if imm5 == 0 then 32 else imm5                                       -- ASR (#0 ⇒ 32)
         (rm.sshiftRight (min n 31), bit rm (min (n - 1) 31))
  | _ => if imm5 == 0 then (((if cin then (1 : Word) else 0) <<< 31) ||| (rm >>> 1), bit rm 0)  -- RRX
         else (rm.rotateRight imm5, bit rm (imm5 - 1))                                 -- ROR

/-- Shifter operand for a register shift amount (low byte of `Rs`). -/
def regShift (rm : Word) (stype amount : Nat) (cin : Bool) : Word × Bool :=
  if amount == 0 then (rm, cin) else
  match stype with
  | 0 => if amount < 32 then (rm <<< amount, bit rm (32 - amount))
         else if amount == 32 then (0, bit rm 0) else (0, false)                       -- LSL
  | 1 => if amount < 32 then (rm >>> amount, bit rm (amount - 1))
         else if amount == 32 then (0, bit rm 31) else (0, false)                      -- LSR
  | 2 => if amount < 32 then (rm.sshiftRight amount, bit rm (amount - 1))
         else (rm.sshiftRight 31, bit rm 31)                                           -- ASR
  | _ => let a := amount % 32                                                          -- ROR
         if a == 0 then (rm, bit rm 31) else (rm.rotateRight a, bit rm (a - 1))

def clz32 (x : Word) : Nat := Id.run do
  for i in [0:32] do
    if (x >>> (31 - i)) &&& 1 == 1 then return i
  return 32

/-- IEEE-754 binary32 compare (bit-pattern; no rounding). Returns NZCV as a 4-bit
    value: unordered=0011, EQ=0110, LT=1000, GT=0010 (ARM A2.5.3). -/
def fcmp32 (a b : Word) : Nat :=
  let isNaN (x : Word) := x &&& 0x7f800000 == 0x7f800000 && x &&& 0x007fffff != 0
  let isZero (x : Word) := x &&& 0x7fffffff == 0
  let key (x : Word) : Nat := if (x >>> 31) &&& 1 == 1 then (~~~ x).toNat else (x ||| 0x80000000).toNat
  if isNaN a || isNaN b then 0b0011
  else if (isZero a && isZero b) || a == b then 0b0110
  else if key a < key b then 0b1000
  else 0b0010

def rotImm (w : Nat) : Nat :=
  let imm8 := w &&& 0xff
  let rot := ((w >>> 8) &&& 0xf) * 2
  if rot == 0 then imm8 else ((imm8 >>> rot) ||| (imm8 <<< (32 - rot))) &&& 0xffffffff

def mnem (w : Nat) : String :=
  let top := (w >>> 25) &&& 0x7
  if top == 0b101 then (if (w >>> 24) &&& 1 == 1 then "BL" else "B")
  else if top == 0b100 then (if (w >>> 20) &&& 1 == 1 then "LDM" else "STM")
  else if (w >>> 24) &&& 0xf == 0b1110 && (w >>> 4) &&& 1 == 1 then
    (if (w >>> 20) &&& 1 == 1 then "MRC" else "MCR")
  else if (w >>> 24) &&& 0xf == 0b1111 then "SVC"
  else if (w >>> 26) &&& 0x3 == 0b01 then (if (w >>> 20) &&& 1 == 1 then "LDR" else "STR")
  else if (w >>> 26) &&& 0x3 == 0b00 then "DP"
  else "UNDEF"

/-- ThumbExpandImm_C (ARM DDI0406C A5.3.2): expand 12-bit T32 modified immediate. -/
def thumbExpandImm (imm12 : Nat) (cin : Bool) : Word × Bool :=
  let imm8 := imm12 &&& 0xff
  match (imm12 >>> 8) &&& 0xf with
  | 0 => (BitVec.ofNat 32 imm8, cin)
  | 1 => (BitVec.ofNat 32 ((imm8 <<< 16) ||| imm8), cin)
  | 2 => (BitVec.ofNat 32 ((imm8 <<< 24) ||| (imm8 <<< 8)), cin)
  | 3 => (BitVec.ofNat 32 ((imm8 <<< 24) ||| (imm8 <<< 16) ||| (imm8 <<< 8) ||| imm8), cin)
  | _ =>
    let rot  := (imm12 >>> 7) &&& 0x1f
    let ival := (imm12 &&& 0x7f) ||| 0x80
    let v : Word := BitVec.ofNat 32
      (if rot == 0 then ival else ((ival >>> rot) ||| (ival <<< (32 - rot))) &&& 0xffffffff)
    (v, bit v 31)

/-- T32 (Thumb-2 / ARMv7 32-bit) instruction decoder.
    hw1 and hw2 are the two 16-bit halfwords (hw1 fetched first at PC, hw2 at PC+2).
    Covers: DP modified-immediate, DP plain-binary (MOVW/MOVT), DP shifted-register,
    load/store single/multiple/dual, multiply, divide, branches, MRS/MSR, hints. -/
def stepThumb32 (hw1 hw2 : Nat) (c : Cpu) (m : Machine) : Cpu × Machine × Bool :=
  let pc    := c.pc
  let next  : Word := pc + 4
  let bump2 (m : Machine) := { m with icount := m.icount + 2 }
  let unsup := ({ c with halted := true },
                bump2 (m.emit (.unsupported pc ((hw1 <<< 16) ||| hw2) "t32")), false)
  let takeDabt (c : Cpu) (m : Machine) :=
    let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" next
    (c, bump2 m, true)
  -- Common fields present in most T32 encodings
  let Rd    := (hw2 >>> 8) &&& 0xf
  let Rn    := hw1 &&& 0xf
  let Rm    := hw2 &&& 0xf
  let rN : Word := c.regs.getD Rn 0
  let rM : Word := c.regs.getD Rm 0
  let sFlg  := (hw1 >>> 4) &&& 1 == 1   -- S (set flags) bit
  -- Write result to Rd; if Rd=15 treat as branch
  let finReg (rd : Nat) (v : Word) :=
    if rd == 15 then
      if c.haltOnSelfBranch && v &&& ~~~1 == pc then
        ({ c with halted := true, blocked := true }, bump2 (m.emit (.note "frontier")), false)
      else ({ c with pc := v &&& ~~~1, tbit := v &&& 1 == 1 }, bump2 m, true)
    else ({ c.setR rd v with pc := next }, bump2 (m.emit (.reg rd v)), true)
  -- ── DP helpers: set flags from result and emit ────────────────────────────
  let dpFlags (s : Bool) (r : Word) (co : Bool) (ov : Bool) : Cpu :=
    if s then { c with n := (r >>> 31) &&& 1 == 1, z := r == 0, c := co, v := ov } else c
  let dpNZC (s : Bool) (r : Word) (co : Bool) : Cpu :=
    if s then setNZ { c with c := co } r else c
  -- Finish a DP instruction writing Rd (skip write if Rd=15 and S=1 → compare form)
  let finDP (s : Bool) (rd : Nat) (r : Word) (flags : Cpu) :=
    if s && rd == 0xf then  -- compare-only variant (TST/TEQ/CMP/CMN): no Rd write
      ({ flags with pc := next }, bump2 m, true)
    else if s then  -- register write + flags update
      ({ flags.setR rd r with pc := next }, bump2 (m.emit (.reg rd r)), true)
    else finReg rd r
  -- ── T32 DP shifted-register (op1=29, bit[25]=1) ───────────────────────────
  if hw1 >>> 11 == 29 && (hw1 >>> 9) &&& 1 == 1 then
    let op4  := (hw1 >>> 5) &&& 0xf
    let s    := sFlg
    let stype := (hw2 >>> 4) &&& 0x3
    let imm5  := ((hw2 >>> 12) &&& 0x7) <<< 2 ||| (hw2 >>> 6) &&& 0x3
    let (sRm, co) := immShift rM stype imm5 c.c
    match op4 with
    | 0x0 => let r := rN &&& sRm; finDP s Rd r (dpNZC s r co)
    | 0x1 => let r := rN &&& ~~~sRm; finDP s Rd r (dpNZC s r co)
    | 0x2 =>
      if Rn == 0xf then finDP s Rd sRm (dpNZC s sRm co)
      else let r := rN ||| sRm; finDP s Rd r (dpNZC s r co)
    | 0x3 =>
      if Rn == 0xf then let v := ~~~sRm; finDP s Rd v (dpNZC s v co)
      else let r := rN ||| ~~~sRm; finDP s Rd r (dpNZC s r co)
    | 0x4 => let r := rN ^^^ sRm; finDP s Rd r (dpNZC s r co)
    | 0x8 =>
      let (r, aco, aov) := addWithCarry rN sRm false
      finDP s Rd r (dpFlags s r aco aov)
    | 0xa =>
      let (r, aco, aov) := addWithCarry rN sRm c.c
      finDP s Rd r (dpFlags s r aco aov)
    | 0xb =>
      let (r, aco, aov) := addWithCarry rN (~~~sRm) c.c
      finDP s Rd r (dpFlags s r aco aov)
    | 0xd =>
      let (r, aco, aov) := addWithCarry rN (~~~sRm) true
      finDP s Rd r (dpFlags s r aco aov)
    | 0xe =>
      let (r, aco, aov) := addWithCarry (~~~rN) sRm true
      finDP s Rd r (dpFlags s r aco aov)
    | _ => unsup
  -- ── T32 branches/BL/misc (op1=30, hw2[15]=1) ────────────────────────────
  else if hw1 >>> 11 == 30 && hw2 >>> 15 == 1 then
    let s    := (hw1 >>> 10) &&& 1
    let j1   := (hw2 >>> 13) &&& 1
    let j2   := (hw2 >>> 11) &&& 1
    let i1   := 1 ^^^ (j1 ^^^ s)
    let i2   := 1 ^^^ (j2 ^^^ s)
    let imm10 := hw1 &&& 0x3ff
    let imm11 := hw2 &&& 0x7ff
    if hw2 >>> 14 == 3 then
      -- BL T1 (hw2[12]=1) or BLX T2 (hw2[12]=0)
      let isBL := (hw2 >>> 12) &&& 1 == 1
      let raw  := (s <<< 24) ||| (i1 <<< 23) ||| (i2 <<< 22) ||| (imm10 <<< 12) ||| (imm11 <<< 1)
      let off  : Word := (BitVec.ofNat 25 raw).signExtend 32
      let tgt  := (pc + 4 + off) &&& (if isBL then ~~~(0 : Word) else ~~~3)
      let lr   := (pc + 4) ||| 1
      if c.haltOnSelfBranch && tgt &&& ~~~1 == pc then
        ({ c.setR 14 lr with halted := true, blocked := true }, bump2 (m.emit (.note "frontier")), false)
      else ({ c.setR 14 lr with pc := tgt &&& ~~~1, tbit := isBL }, bump2 m, true)
    else if hw2 >>> 12 == 0x9 || hw2 >>> 12 == 0xb then
      -- B.W T4 unconditional (hw2[15:14]=10, hw2[12]=1: can be 1001 or 1011)
      let raw  := (s <<< 24) ||| (i1 <<< 23) ||| (i2 <<< 22) ||| (imm10 <<< 12) ||| (imm11 <<< 1)
      let off  : Word := (BitVec.ofNat 25 raw).signExtend 32
      let tgt  := pc + 4 + off
      if c.haltOnSelfBranch && tgt == pc then
        ({ c with halted := true, blocked := true }, bump2 (m.emit (.note "frontier")), false)
      else ({ c with pc := tgt }, bump2 m, true)
    else if (hw2 >>> 12 == 0x8 || hw2 >>> 12 == 0xa) && (hw1 >>> 6) &&& 0xf >= 14 then
      -- Misc: hw2[12]=0 AND cond=14/15 → MRS/MSR/NOP/barriers (not a valid conditional branch)
      if (hw1 &&& 0xFFF0) == 0xF3E0 then
        -- MRS: read CPSR (hw1=F3EF) or SPSR (hw1=F3FF)
        -- ARM ARM: T/I/F bits are UNPREDICTABLE in MRS result; mask them to match oracle
        let srcSpsr := hw1 &&& 0x10 == 0x10
        let v := (if srcSpsr then spsrGet c c.mode else packCpsr c) &&& ~~~(BitVec.ofNat 32 0xE0)
        finReg Rd v
      else if (hw1 &&& 0xFF00) == 0xF300 then
        -- MSR: write PSR fields (F380..F3FF without the MRS patterns)
        let dstSpsr := (hw2 >>> 8) &&& 1 == 0  -- CPSR or SPSR
        let mask := (hw2 >>> 8) &&& 0xf
        let c' := if mask &&& 8 != 0 then
          unpackCpsr c (rN &&& 0xff000000 ||| (packCpsr c &&& 0x00ffffff)) else c
        let c' := if mask &&& 1 != 0 then
          unpackCpsr c' (packCpsr c' &&& 0xffffff00 ||| (rN &&& 0xff)) else c'
        ({ c' with pc := next }, bump2 m, true)
      else if hw1 == 0xF3AF then
        -- NOP-class hints (WFI/WFE/SEV/NOP)
        ({ c with pc := next }, bump2 m, true)
      else if hw1 == 0xF3BF then
        -- DMB/DSB/ISB memory barriers → NOP (pure functional model)
        ({ c with pc := next }, bump2 m, true)
      else
        ({ c with pc := next }, bump2 m, true)  -- unknown misc → NOP
    else if hw2 >>> 12 == 0x8 || hw2 >>> 12 == 0xa then
      -- B.W T3 conditional (hw2[15:14]=10, hw2[12]=0, cond<14)
      let cond  := (hw1 >>> 6) &&& 0xf
      let imm6  := hw1 &&& 0x3f
      let raw   := (s <<< 20) ||| (j1 <<< 18) ||| (j2 <<< 16) ||| (imm6 <<< 11) ||| (imm11 <<< 1)
      let off   : Word := (BitVec.ofNat 21 raw).signExtend 32
      let tgt   := pc + 4 + off
      if condHolds c cond then
        if c.haltOnSelfBranch && tgt == pc then
          ({ c with halted := true, blocked := true }, bump2 (m.emit (.note "frontier")), false)
        else ({ c with pc := tgt }, bump2 m, true)
      else ({ c with pc := next }, bump2 m, true)
    else ({ c with pc := next }, bump2 m, true)  -- unknown branch/misc → NOP
  -- ── T32 DP modified immediate (op1=30, bit[25]=0, hw2[15]=0) ─────────────
  else if hw1 >>> 11 == 30 && (hw1 >>> 9) &&& 1 == 0 && hw2 >>> 15 == 0 then
    let op4 := (hw1 >>> 5) &&& 0xf
    let s   := sFlg
    let i12 := ((hw1 >>> 10) &&& 1) <<< 11 ||| ((hw2 >>> 12) &&& 7) <<< 8 ||| hw2 &&& 0xff
    let (imm, cin) := thumbExpandImm i12 c.c
    match op4 with
    | 0x0 => let r := rN &&& imm; finDP s Rd r (dpNZC s r cin)
    | 0x1 => let r := rN &&& ~~~imm; finDP s Rd r (dpNZC s r cin)
    | 0x2 =>
      if Rn == 0xf then finDP s Rd imm (dpNZC s imm cin)
      else let r := rN ||| imm; finDP s Rd r (dpNZC s r cin)
    | 0x3 =>
      if Rn == 0xf then let v := ~~~imm; finDP s Rd v (dpNZC s v cin)
      else let r := rN ||| ~~~imm; finDP s Rd r (dpNZC s r cin)
    | 0x4 => let r := rN ^^^ imm; finDP s Rd r (dpNZC s r cin)
    | 0x8 =>
      let (r, aco, aov) := addWithCarry rN imm false
      finDP s Rd r (dpFlags s r aco aov)
    | 0xa =>
      let (r, aco, aov) := addWithCarry rN imm c.c
      finDP s Rd r (dpFlags s r aco aov)
    | 0xb =>
      let (r, aco, aov) := addWithCarry rN (~~~imm) c.c
      finDP s Rd r (dpFlags s r aco aov)
    | 0xd =>
      let (r, aco, aov) := addWithCarry rN (~~~imm) true
      finDP s Rd r (dpFlags s r aco aov)
    | 0xe =>
      let (r, aco, aov) := addWithCarry (~~~rN) imm true
      finDP s Rd r (dpFlags s r aco aov)
    | _ => unsup
  -- ── T32 DP plain binary immediate (op1=30, bit[25]=1, hw2[15]=0) ──────────
  else if hw1 >>> 11 == 30 && (hw1 >>> 9) &&& 1 == 1 && hw2 >>> 15 == 0 then
    -- Sub-op: bits[25:20] = (hw1 >>> 4) &&& 0x3f
    let subop := (hw1 >>> 4) &&& 0x3f
    let i     := (hw1 >>> 10) &&& 1
    let imm3  := (hw2 >>> 12) &&& 7
    let imm8  := hw2 &&& 0xff
    -- imm12 for ADDW/SUBW includes the i bit at position 11
    let imm12 : Word := BitVec.ofNat 32 (i <<< 11 ||| imm3 <<< 8 ||| imm8)
    match subop with
    | 0x20 =>  -- ADDW: Rd = PC+imm12 if Rn=f (ADR T3), else Rn+imm12 (no flags)
      let base := if Rn == 0xf then (pc + 4) &&& ~~~3 else rN
      finReg Rd (base + imm12)
    | 0x24 =>  -- MOVW: Rd = ZeroExtend(imm16, 32); imm16 = {imm4, i, imm3, imm8}
      let imm16 := (Rn <<< 12) ||| (i <<< 11) ||| (imm3 <<< 8) ||| imm8
      finReg Rd (BitVec.ofNat 32 imm16)
    | 0x2a =>  -- SUBW: Rd = Rn - imm12; if Rn=f → ADR T2 (pc - imm)
      let base := if Rn == 0xf then (pc + 4) &&& ~~~3 else rN
      finReg Rd (base - imm12)
    | 0x2c =>  -- MOVT: Rd[31:16] = imm16; imm16 = {imm4, i, imm3, imm8}
      let imm16 := (Rn <<< 12) ||| (i <<< 11) ||| (imm3 <<< 8) ||| imm8
      let prev  := c.regs.getD Rd 0
      finReg Rd ((BitVec.ofNat 32 (imm16 <<< 16)) ||| (prev &&& 0x0000ffff))
    | 0x34 =>  -- SBFX: Rd = SignExtend(Rn[lsb+width-1:lsb], 32)
      let lsb := ((hw2 >>> 12) &&& 7) <<< 2 ||| (hw2 >>> 6) &&& 3
      let wm1 := hw2 &&& 0x1f
      let extracted := (rN >>> lsb) &&& BitVec.ofNat 32 ((1 <<< (wm1 + 1)) - 1)
      finReg Rd ((BitVec.ofNat (wm1 + 1) extracted.toNat).signExtend 32)
    | 0x36 =>  -- BFI/BFC
      let lsb := ((hw2 >>> 12) &&& 7) <<< 2 ||| (hw2 >>> 6) &&& 3
      let msb := hw2 &&& 0x1f
      let width := msb - lsb + 1
      let mask  : Word := (BitVec.ofNat 32 ((1 <<< width) - 1)) <<< lsb
      let src   : Word := if Rn == 0xf then 0 else rN
      finReg Rd ((c.regs.getD Rd 0 &&& ~~~mask) ||| ((src <<< lsb) &&& mask))
    | 0x3c =>  -- UBFX: Rd = ZeroExtend(Rn[lsb+width-1:lsb], 32)
      let lsb := ((hw2 >>> 12) &&& 7) <<< 2 ||| (hw2 >>> 6) &&& 3
      let wm1 := hw2 &&& 0x1f
      finReg Rd ((rN >>> lsb) &&& BitVec.ofNat 32 ((1 <<< (wm1 + 1)) - 1))
    | 0x30 | 0x32 =>  -- SSAT T1: signed saturation (sh=0→LSL, sh=1→ASR)
      let sh    := subop &&& 2 != 0
      let shAmt := (imm3 <<< 2) ||| ((hw2 >>> 6) &&& 3)
      let satN  := hw2 &&& 0x1f  -- SatWidth - 1; range = [-2^satN, 2^satN-1]
      let op  : Int := if sh then rN.toInt.shiftRight shAmt else (rN <<< shAmt).toInt
      let lo  : Int := -(Int.ofNat (1 <<< satN))
      let hi  : Int := Int.ofNat ((1 <<< satN) - 1)
      let r   : Int := if op < lo then lo else if op > hi then hi else op
      finReg Rd (BitVec.ofInt 32 r)
    | 0x38 | 0x3a =>  -- USAT T1: unsigned saturation (sh=0→LSL, sh=1→ASR)
      let sh    := subop &&& 2 != 0
      let shAmt := (imm3 <<< 2) ||| ((hw2 >>> 6) &&& 3)
      let satW  := hw2 &&& 0x1f  -- SatWidth directly; range = [0, 2^satW-1]
      let op  : Int := if sh then rN.toInt.shiftRight shAmt else (rN <<< shAmt).toInt
      let hi  : Int := Int.ofNat ((1 <<< satW) - 1)
      let r   : Int := if op < 0 then 0 else if op > hi then hi else op
      finReg Rd (BitVec.ofInt 32 r)
    | _ => unsup
  -- ── T32 load/store multiple (op1=29, bit[25]=0, bit[24]=0) ───────────────
  else if hw1 >>> 11 == 29 && (hw1 >>> 9) &&& 1 == 0 && (hw1 >>> 6) &&& 1 == 0 then
    let ld    := (hw1 >>> 4) &&& 1 == 1   -- L bit
    let wb    := (hw1 >>> 5) &&& 1 == 1   -- W (writeback)
    let pu    := (hw1 >>> 7) &&& 0x3       -- P:U bits (00=DA, 01=IA, 10=DB, 11=IB)
    let regl  := hw2 &&& 0x7fff            -- register list bits [14:0]
    let pcBit := (hw2 >>> 15) &&& 1 == 1  -- bit[15] = PC
    let lrBit := (hw2 >>> 14) &&& 1 == 1  -- bit[14] = LR
    let regs  := (List.range 15).filter (fun i => (regl >>> i) &&& 1 == 1)
    let base  := rN
    let count := regs.length + (if pcBit then 1 else 0) + (if lrBit && !ld then 1 else 0)
    let startAddr : Word := match pu with
      | 0 => base - BitVec.ofNat 32 (count * 4)  -- DA: post-decrement (end addr)
      | 2 => base - BitVec.ofNat 32 (count * 4)  -- DB: pre-decrement
      | 1 => base                                   -- IA: start = base
      | _ => base + 4                               -- IB: start = base+4
    if ld then
      let (c', m') := Id.run do
        let mut c' := c; let mut m' := m; let mut idx := 0
        for r in regs do
          let (res, mm) := c'.memRead m' (startAddr + BitVec.ofNat 32 (idx * 4)) 32
          m' := mm; if let .ok v := res then c' := c'.setR r v; idx := idx + 1
        if lrBit then  -- LR in list for LDM → load into LR
          let (res, mm) := c'.memRead m' (startAddr + BitVec.ofNat 32 (idx * 4)) 32
          m' := mm; if let .ok v := res then c' := c'.setR 14 v; idx := idx + 1
        return (c', m')
      let (c'', m'') :=
        if pcBit then
          let (res, mm) := c'.memRead m' (startAddr + BitVec.ofNat 32 (regs.length * 4)) 32
          match res with
          | .error _ => (c', m')
          | .ok v => ({ c' with pc := v &&& ~~~1, tbit := v &&& 1 == 1 }, mm)
        else (c', m')
      let newBase : Word := match pu with
        | 0 => base - BitVec.ofNat 32 (count * 4)
        | 2 => base - BitVec.ofNat 32 (count * 4)
        | _ => base + BitVec.ofNat 32 (count * 4)
      let c3 := if wb && !pcBit then c''.setR Rn newBase else c''
      let c3 := if !pcBit then { c3 with pc := next } else c3
      (c3, bump2 m'', true)
    else
      let allRegs := regs ++ (if lrBit then [14] else [])
      let m' := Id.run do
        let mut m' := m; let mut idx := 0
        for r in allRegs do
          let (_, mm) := c.memWrite m' (startAddr + BitVec.ofNat 32 (idx * 4)) (c.regs.getD r 0) 32
          m' := mm; idx := idx + 1
        if pcBit then
          let (_, mm) := c.memWrite m' (startAddr + BitVec.ofNat 32 (allRegs.length * 4)) (pc + 4 ||| 1) 32
          m' := mm
        return m'
      let newBase : Word := match pu with
        | 0 => base - BitVec.ofNat 32 (count * 4)
        | 2 => base - BitVec.ofNat 32 (count * 4)
        | _ => base + BitVec.ofNat 32 (count * 4)
      let c' := if wb then c.setR Rn newBase else c
      ({ c' with pc := next }, bump2 m', true)
  -- ── T32 load/store dual/exclusive (op1=29, bit[25]=0, bit[24]=0 range) ────
  -- LDRD / STRD (T1) and LDREX/STREX: hw1[8:7] = {P,U} with specific W/L combos
  else if hw1 >>> 11 == 29 && (hw1 >>> 9) &&& 1 == 0 then
    -- Covers: LDRD (bit[6]=1,L=1), STRD (bit[6]=1,L=0), LDREX, STREX
    let isPU  := (hw1 >>> 7) &&& 0x3   -- P:U
    let isW   := (hw1 >>> 5) &&& 1 == 1
    let isL   := (hw1 >>> 4) &&& 1 == 1
    let isD   := (hw1 >>> 6) &&& 1 == 1   -- dual register (LDRD/STRD)
    if isD then
      if (isPU &&& 2) == 0 && !isW then
        -- LDREX / STREX (P=0, W=0)
        let Rt_ex := (hw2 >>> 12) &&& 0xf
        let addr := rN + BitVec.ofNat 32 ((hw2 &&& 0xff) * 4)
        if isL then
          let (res, m') := c.memRead m addr 32
          match res with
          | .error _ => takeDabt c m
          | .ok v => ({ c.setR Rt_ex v with pc := next, exclReserved := true }, bump2 m', true)
        else
          if c.exclReserved then
            let (_, m') := c.memWrite m addr (c.regs.getD Rt_ex 0) 32
            ({ c.setR Rd 0 with pc := next, exclReserved := false }, bump2 m', true)
          else
            ({ c.setR Rd 1 with pc := next }, bump2 m, true)
      else
        -- LDRD / STRD: Rt=hw2[15:12], Rt2=hw2[11:8]
        let Rt   := (hw2 >>> 12) &&& 0xf
        let Rt2  := (hw2 >>>  8) &&& 0xf
        let imm8 : Word := BitVec.ofNat 32 ((hw2 &&& 0xff) * 4)
        let addr := if isPU &&& 1 == 1 then rN + imm8 else rN - imm8  -- U bit
        let pre  := (isPU >>> 1) &&& 1 == 1  -- P bit
        let effA := if pre then addr else rN
        if isL then
          let (r1, m') := c.memRead m effA 32
          let (r2, m'') := c.memRead m' (effA + 4) 32
          match r1, r2 with
          | .ok v1, .ok v2 =>
            let c' := (c.setR Rt v1).setR Rt2 v2
            let c' := if isW then c'.setR Rn addr else c'
            ({ c' with pc := next }, bump2 m'', true)
          | _, _ => takeDabt c m
        else
          let (_, m') := c.memWrite m effA (c.regs.getD Rt 0) 32
          let (_, m'') := c.memWrite m' (effA + 4) (c.regs.getD Rt2 0) 32
          let c' := if isW then c.setR Rn addr else c
          ({ c' with pc := next }, bump2 m'', true)
    else
      unsup  -- isD=0 in this range: not a currently supported instruction
  -- ── T32 load/store single (op1=31) ────────────────────────────────────────
  else if hw1 >>> 11 == 31 && (hw1 >>> 9) &&& 1 == 0 then
    -- op1[4:1] in hw1[8:5] identifies the access size/type
    let op8 := (hw1 >>> 4) &&& 0xf   -- bits[23:20]
    let isLd := op8 &&& 1 == 1
    -- Data register is always hw2[15:12] (Rt) for all T32 load/store single forms
    let Rt_ls := (hw2 >>> 12) &&& 0xf
    match (op8 >>> 1) &&& 0x7 with
    | 0x0 =>  -- STRB T2/T4 (0000) / LDRB T2/T4 (0001)
      let isSigned := (op8 >>> 2) &&& 1 == 1
      if (hw2 >>> 11) &&& 1 == 1 then  -- T4: 8-bit imm with P/U/W (hw2[11]=1)
        let off : Word := BitVec.ofNat 32 (hw2 &&& 0xff)
        let u   := (hw2 >>> 9) &&& 1 == 1
        let p   := (hw2 >>> 10) &&& 1 == 1
        let w   := (hw2 >>> 8) &&& 1 == 1
        let ea  : Word := if u then rN + off else rN - off
        let addr := if p then ea else rN
        if isLd then
          let (res, m') := c.memRead m addr 8
          match res with
          | .error _ => takeDabt c m
          | .ok v =>
            let ext := if isSigned then (BitVec.ofNat 8 v.toNat).signExtend 32 else v
            let c' := if w then c.setR Rn ea else c
            ({ c'.setR Rt_ls ext with pc := next }, bump2 m', true)
        else
          let (_, m') := c.memWrite m addr (c.regs.getD Rt_ls 0) 8
          ({ (if w then c.setR Rn ea else c) with pc := next }, bump2 m', true)
      else  -- T2: register with shift (hw2[11]=0)
        let sh := (hw2 >>> 4) &&& 3
        let (sval, _) := immShift rM 0 sh false
        let addr := rN + sval
        if isLd then
          let (res, m') := c.memRead m addr 8
          match res with
          | .error _ => takeDabt c m
          | .ok v =>
            let ext := if isSigned then (BitVec.ofNat 8 v.toNat).signExtend 32 else v
            ({ c.setR Rt_ls ext with pc := next }, bump2 m', true)
        else
          let (_, m') := c.memWrite m addr (c.regs.getD Rt_ls 0) 8
          ({ c with pc := next }, bump2 m', true)
    | 0x1 =>  -- STRH T2/T4 (0010) / LDRH T2/T4 (0011) — register or 8-bit imm
      let isSigned := (op8 >>> 2) &&& 1 == 1
      if (hw2 >>> 11) &&& 1 == 1 then  -- T4: 8-bit imm with P/U/W
        let off : Word := BitVec.ofNat 32 (hw2 &&& 0xff)
        let u   := (hw2 >>> 9) &&& 1 == 1
        let p   := (hw2 >>> 10) &&& 1 == 1
        let w   := (hw2 >>> 8) &&& 1 == 1
        let ea  : Word := if u then rN + off else rN - off
        let addr := if p then ea else rN
        if isLd then
          let (res, m') := c.memRead m addr 16
          match res with
          | .error _ => takeDabt c m
          | .ok v =>
            let ext := if isSigned then (BitVec.ofNat 16 v.toNat).signExtend 32 else v
            let c' := if w then c.setR Rn ea else c
            ({ c'.setR Rt_ls ext with pc := next }, bump2 m', true)
        else
          let (_, m') := c.memWrite m addr (c.regs.getD Rt_ls 0) 16
          ({ (if w then c.setR Rn ea else c) with pc := next }, bump2 m', true)
      else  -- T2: register with shift (always LSL)
        let sh := (hw2 >>> 4) &&& 3
        let (sval, _) := immShift rM 0 sh false
        let addr := rN + sval
        if isLd then
          let (res, m') := c.memRead m addr 16
          match res with
          | .error _ => takeDabt c m
          | .ok v =>
            let ext := if isSigned then (BitVec.ofNat 16 v.toNat).signExtend 32 else v
            ({ c.setR Rt_ls ext with pc := next }, bump2 m', true)
        else
          let (_, m') := c.memWrite m addr (c.regs.getD Rt_ls 0) 16
          ({ c with pc := next }, bump2 m', true)
    | 0x2 =>  -- STR T2/T4 (0100) / LDR T2/T4 (0101) — register or 8-bit imm
      if (hw2 >>> 11) &&& 1 == 1 then  -- T4: hw2[11]=1, 8-bit imm with P/U/W
        let off : Word := BitVec.ofNat 32 (hw2 &&& 0xff)
        let u   := (hw2 >>> 9) &&& 1 == 1
        let p   := (hw2 >>> 10) &&& 1 == 1
        let w   := (hw2 >>> 8) &&& 1 == 1
        let ea  : Word := if u then rN + off else rN - off
        let addr := if p then ea else rN
        if isLd then
          let (res, m') := c.memRead m addr 32
          match res with
          | .error _ => takeDabt c m
          | .ok v =>
            let c' := if w then c.setR Rn ea else c
            if Rt_ls == 15 then
              ({ c' with pc := v &&& ~~~1, tbit := v &&& 1 == 1 }, bump2 m', true)
            else ({ c'.setR Rt_ls v with pc := next }, bump2 (m'.emit (.reg Rt_ls v)), true)
        else
          let (_, m') := c.memWrite m addr (c.regs.getD Rt_ls 0) 32
          ({ (if w then c.setR Rn ea else c) with pc := next }, bump2 m', true)
      else  -- T2: hw2[11]=0, register with LSL shift
        let (sval, _) := immShift rM 0 ((hw2 >>> 4) &&& 3) false
        let addr := rN + sval
        if isLd then
          let (res, m') := c.memRead m addr 32
          match res with
          | .error _ => takeDabt c m
          | .ok v => finReg Rt_ls v
        else
          let (_, m') := c.memWrite m addr (c.regs.getD Rt_ls 0) 32
          ({ c with pc := next }, bump2 m', true)
    | 0x4 =>  -- STRB T3 (1000) / LDRB T3 (1001) / LDRSB T3 (from 0xF990)
      let isSigned := (hw1 >>> 8) &&& 1 == 1  -- hw1[8]=1 for 0xF9xx (signed)
      let addr := rN + BitVec.ofNat 32 (hw2 &&& 0xfff)
      if isLd then
        let (res, m') := c.memRead m addr 8
        match res with
        | .error _ => takeDabt c m
        | .ok v =>
          let ext := if isSigned then (BitVec.ofNat 8 v.toNat).signExtend 32 else v
          ({ c.setR Rt_ls ext with pc := next }, bump2 m', true)
      else
        let (_, m') := c.memWrite m addr (c.regs.getD Rt_ls 0) 8
        ({ c with pc := next }, bump2 m', true)
    | 0x5 =>  -- STRH T3 (1010) / LDRH T3 (1011) / LDRSH T3 (from 0xF9B0)
      let isSigned := (hw1 >>> 8) &&& 1 == 1
      let addr := rN + BitVec.ofNat 32 (hw2 &&& 0xfff)
      if isLd then
        let (res, m') := c.memRead m addr 16
        match res with
        | .error _ => takeDabt c m
        | .ok v =>
          let ext := if isSigned then (BitVec.ofNat 16 v.toNat).signExtend 32 else v
          ({ c.setR Rt_ls ext with pc := next }, bump2 m', true)
      else
        let (_, m') := c.memWrite m addr (c.regs.getD Rt_ls 0) 16
        ({ c with pc := next }, bump2 m', true)
    | 0x6 =>  -- STR T3 (1100) / LDR T3 (1101) — 12-bit unsigned immediate
      let addr := rN + BitVec.ofNat 32 (hw2 &&& 0xfff)
      if isLd then
        let (res, m') := c.memRead m addr 32
        match res with
        | .error _ => takeDabt c m
        | .ok v => finReg Rt_ls v
      else
        let (_, m') := c.memWrite m addr (c.regs.getD Rt_ls 0) 32
        ({ c with pc := next }, bump2 m', true)
    | _ => unsup
  -- ── T32 multiply / divide (op1=31, identified by hw1 bits) ───────────────
  else if hw1 >>> 11 == 31 && (hw1 >>> 7) &&& 1 == 1 then
    -- Long multiply, divide: hw1[7]=1
    let op := (hw1 >>> 4) &&& 0x7
    let Ra := (hw2 >>> 12) &&& 0xf
    let Rdhi := Rd; let Rdlo := Ra
    match op with
    | 0 =>  -- SMULL: signed 64-bit product
      let prod := (rN.toInt * rM.toInt)
      let lo : Word := BitVec.ofInt 32 prod
      let hi : Word := BitVec.ofInt 32 (prod.shiftRight 32)
      ({ (c.setR Rdlo lo).setR Rdhi hi with pc := next }, bump2 m, true)
    | 2 =>  -- UMULL
      let prod := rN.toNat * rM.toNat
      let lo : Word := BitVec.ofNat 32 (prod % 0x100000000)
      let hi : Word := BitVec.ofNat 32 (prod / 0x100000000)
      ({ (c.setR Rdlo lo).setR Rdhi hi with pc := next }, bump2 m, true)
    | 4 =>  -- SMLAL: signed product + signed-hi/unsigned-lo accumulator
      let prod := (rN.toInt * rM.toInt)
      let acc : Int := (c.regs.getD Rdhi 0).toInt * 0x100000000 + Int.ofNat (c.regs.getD Rdlo 0).toNat
      let tot := prod + acc
      let lo : Word := BitVec.ofInt 32 tot
      let hi : Word := BitVec.ofInt 32 (tot.shiftRight 32)
      ({ (c.setR Rdlo lo).setR Rdhi hi with pc := next }, bump2 m, true)
    | 6 =>  -- UMLAL
      let prod := rN.toNat * rM.toNat
      let acc : Nat := (c.regs.getD Rdhi 0).toNat * 0x100000000 + (c.regs.getD Rdlo 0).toNat
      let tot := prod + acc
      let lo : Word := BitVec.ofNat 32 (tot % 0x100000000)
      let hi : Word := BitVec.ofNat 32 (tot / 0x100000000)
      ({ (c.setR Rdlo lo).setR Rdhi hi with pc := next }, bump2 m, true)
    | 1 =>  -- SDIV (truncate toward zero)
      if rM == 0 then ({ c.setR Rd 0 with pc := next }, bump2 m, true)
      else
        let q := rN.toInt / rM.toInt
        ({ c.setR Rd (BitVec.ofInt 32 q) with pc := next }, bump2 m, true)
    | 3 =>  -- UDIV
      if rM == 0 then ({ c.setR Rd 0 with pc := next }, bump2 m, true)
      else ({ c.setR Rd (BitVec.ofNat 32 (rN.toNat / rM.toNat)) with pc := next }, bump2 m, true)
    | _ => unsup
  -- ── T32 extend-with-rotate + CLZ (op1=31, hw1=0xFAxx) ───────────────────
  else if hw1 >>> 11 == 31 && (hw1 >>> 8) &&& 0xf == 0xa then
    let op  := (hw1 >>> 4) &&& 0xf
    let rot := ((hw2 >>> 4) &&& 3) * 8  -- rotation: 0, 8, 16, or 24 bits
    let rotated : Word := if rot == 0 then rM else (rM >>> rot) ||| (rM <<< (32 - rot))
    let addN : Word := if Rn == 0xf then 0 else rN  -- 0 for non-add form (Rn=PC)
    match op with
    | 0 =>  -- SXTH / SXTAH
      finReg Rd (addN + (BitVec.ofNat 16 (rotated &&& 0xffff).toNat).signExtend 32)
    | 1 =>  -- UXTH / UXTAH
      finReg Rd (addN + (rotated &&& 0xffff))
    | 2 =>  -- SXTB16 / SXTAB16: sign-extend bytes 0 and 2 into halfwords 0 and 1
      let lo := (BitVec.ofNat 8 (rotated &&& 0xff).toNat).signExtend 16
      let hi := (BitVec.ofNat 8 ((rotated >>> 16) &&& 0xff).toNat).signExtend 16
      let blo : Word := if Rn == 0xf then 0 else rN &&& 0xffff
      let bhi : Word := if Rn == 0xf then 0 else (rN >>> 16) &&& 0xffff
      finReg Rd (((blo + lo.zeroExtend 32) &&& 0xffff) ||| (((bhi + hi.zeroExtend 32) &&& 0xffff) <<< 16))
    | 3 =>  -- UXTB16 / UXTAB16: zero-extend bytes 0 and 2 into halfwords 0 and 1
      let lo : Word := rotated &&& 0xff
      let hi : Word := (rotated >>> 16) &&& 0xff
      let blo : Word := if Rn == 0xf then 0 else rN &&& 0xffff
      let bhi : Word := if Rn == 0xf then 0 else (rN >>> 16) &&& 0xffff
      finReg Rd (((blo + lo) &&& 0xffff) ||| (((bhi + hi) &&& 0xffff) <<< 16))
    | 4 =>  -- SXTB / SXTAB
      finReg Rd (addN + (BitVec.ofNat 8 (rotated &&& 0xff).toNat).signExtend 32)
    | 5 =>  -- UXTB / UXTAB
      finReg Rd (addN + (rotated &&& 0xff))
    | 0xb =>  -- CLZ
      finReg Rd (BitVec.ofNat 32 (clz32 rM))
    | _ => unsup
  -- ── T32 multiply (32-bit result): op1=31, hw1[7]=0 ───────────────────────
  else if hw1 >>> 11 == 31 && (hw1 >>> 7) &&& 1 == 0 then
    let op := (hw1 >>> 4) &&& 0xf
    let Ra := (hw2 >>> 12) &&& 0xf
    match op with
    | 0 =>  -- MUL (Ra=f) / MLA / MLS (distinguished by hw2[4])
      if Ra == 0xf then
        let r := rN * rM
        ({ c.setR Rd r with pc := next }, bump2 (m.emit (.reg Rd r)), true)
      else if (hw2 >>> 4) &&& 1 == 1 then  -- MLS: hw2[4]=1
        let r := c.regs.getD Ra 0 - rN * rM
        ({ c.setR Rd r with pc := next }, bump2 (m.emit (.reg Rd r)), true)
      else  -- MLA: hw2[4]=0
        let r := rN * rM + c.regs.getD Ra 0
        ({ c.setR Rd r with pc := next }, bump2 (m.emit (.reg Rd r)), true)
    | _ => unsup
  else unsup

/-- Full T16 (Thumb-1 + ARMv6 extensions) instruction decoder, following ARM DDI 0100. -/
def stepThumb (c : Cpu) (m : Machine) : Cpu × Machine × Bool :=
  let pc := c.pc
  let (fres, m) := c.memRead m pc 16 (fetch := true)
  match fres with
  | .error _ => ({ c with halted := true }, m.emit (.note "fetch_fault"), false)
  | .ok hw =>
    let w   := hw.toNat &&& 0xffff
    let m   := m.emit (.exec pc (BitVec.ofNat 8 1) "thumb")
    let bump (m : Machine) : Machine := { m with icount := m.icount + 1 }
    let next : Word := pc + 2
    -- PC read value in Thumb: PC+4, word-aligned (used for PC-relative addressing)
    let pcR : Word := (pc + 4) &&& ~~~2
    -- register read 0–15; r15 → pcR
    let rRd (i : Nat) : Word := if i == 15 then pcR else c.regs.getD i 0
    -- data abort helper: take dabt exception, count the faulting instruction
    let takeDabt (c : Cpu) (m : Machine) :=
      let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" next
      (c, bump m, true)
    -- ── 000: shift immediate / add-subtract ──────────────────────────────────
    if (w >>> 13) == 0 then
      let stype := (w >>> 11) &&& 0x3
      let rd := w &&& 0x7
      if stype <= 2 then           -- LSL / LSR / ASR immediate
        let rm := c.regs.getD ((w >>> 3) &&& 0x7) 0
        let imm5 := (w >>> 6) &&& 0x1f
        let (v, cout) := immShift rm stype imm5 c.c
        let c' := { (setNZ c v) with c := cout, pc := next }
        (c'.setR rd v, bump (m.emit (.reg rd v)), true)
      else                         -- Add / Subtract (bits[12:11]=11)
        let iImm := (w >>> 10) &&& 1 == 1
        let iSub := (w >>> 9)  &&& 1 == 1
        let rn   := c.regs.getD ((w >>> 3) &&& 0x7) 0
        let b : Word := if iImm then BitVec.ofNat 32 ((w >>> 6) &&& 0x7)
                        else c.regs.getD ((w >>> 6) &&& 0x7) 0
        let r := if iSub then rn - b else rn + b
        let c' := ((if iSub then setSubFlags else setAddFlags) c rn b r).setR rd r
        ({ c' with pc := next }, bump (m.emit (.reg rd r)), true)
    -- ── 001: MOV / CMP / ADD / SUB immediate ─────────────────────────────────
    else if (w >>> 13) == 1 then
      let op  := (w >>> 11) &&& 0x3
      let rdn := (w >>> 8)  &&& 0x7
      let imm : Word := BitVec.ofNat 32 (w &&& 0xff)
      let a := c.regs.getD rdn 0
      match op with
      | 0 => let c' := (setNZ c imm).setR rdn imm           -- MOVS
             ({ c' with pc := next }, bump (m.emit (.reg rdn imm)), true)
      | 1 => let r := a - imm                                -- CMP (no write)
             ({ (setSubFlags c a imm r) with pc := next }, bump m, true)
      | 2 => let r := a + imm                                -- ADDS
             let c' := (setAddFlags c a imm r).setR rdn r
             ({ c' with pc := next }, bump (m.emit (.reg rdn r)), true)
      | _ => let r := a - imm                                -- SUBS
             let c' := (setSubFlags c a imm r).setR rdn r
             ({ c' with pc := next }, bump (m.emit (.reg rdn r)), true)
    -- ── 010000: ALU data-processing ──────────────────────────────────────────
    else if (w >>> 10) == 0b010000 then
      let op  := (w >>> 6) &&& 0xf
      let rm  := c.regs.getD ((w >>> 3) &&& 0x7) 0
      let rdn := w &&& 0x7
      let a   := c.regs.getD rdn 0
      let fin (r : Word) (c' : Cpu) :=
        ({ c'.setR rdn r with pc := next }, bump (m.emit (.reg rdn r)), true)
      let fcmp (c' : Cpu) := ({ c' with pc := next }, bump m, true)
      match op with
      | 0x0 => fin (a &&& rm) (setNZ c (a &&& rm))
      | 0x1 => fin (a ^^^ rm) (setNZ c (a ^^^ rm))
      | 0x2 => let (v,co) := regShift a 0 (rm.toNat &&& 0xff) c.c
               fin v { setNZ c v with c := co }
      | 0x3 => let (v,co) := regShift a 1 (rm.toNat &&& 0xff) c.c
               fin v { setNZ c v with c := co }
      | 0x4 => let (v,co) := regShift a 2 (rm.toNat &&& 0xff) c.c
               fin v { setNZ c v with c := co }
      | 0x5 => let (r,co,ov) := addWithCarry a rm c.c
               fin r { c with n:=(r>>>31)&&&1==1, z:=r==0, c:=co, v:=ov }
      | 0x6 => let (r,co,ov) := addWithCarry a (~~~rm) c.c  -- SBC: a+~rm+C
               fin r { c with n:=(r>>>31)&&&1==1, z:=r==0, c:=co, v:=ov }
      | 0x7 => let (v,co) := regShift a 3 (rm.toNat &&& 0xff) c.c
               fin v { setNZ c v with c := co }
      | 0x8 => fcmp (setNZ c (a &&& rm))                    -- TST
      | 0x9 => let r : Word := 0 - rm                       -- NEG/RSB #0
               fin r (setSubFlags c 0 rm r)
      | 0xa => let r := a - rm                              -- CMP
               fcmp (setSubFlags c a rm r)
      | 0xb => let r := a + rm                              -- CMN
               fcmp (setAddFlags c a rm r)
      | 0xc => fin (a ||| rm) (setNZ c (a ||| rm))
      | 0xd => let r := a * rm; fin r (setNZ c r)           -- MUL
      | 0xe => fin (a &&& ~~~rm) (setNZ c (a &&& ~~~rm))    -- BIC
      | _   => fin (~~~rm) (setNZ c (~~~rm))                -- MVN
    -- ── 010001: special data + BX/BLX ────────────────────────────────────────
    else if (w >>> 10) == 0b010001 then
      let op  := (w >>> 8) &&& 0x3
      let rm  := (w >>> 3) &&& 0xf
      let rdn := ((w >>> 7) &&& 1) <<< 3 ||| (w &&& 0x7)
      let rmV := rRd rm
      match op with
      | 0 =>   -- ADD high (no flags)
        let r := rRd rdn + rmV
        if rdn == 15 then
          if c.haltOnSelfBranch && r &&& ~~~1 == pc then
            ({ c with halted := true, blocked := true }, bump (m.emit (.note "frontier")), false)
          else ({ c with pc := r &&& ~~~1, tbit := r &&& 1 == 1 }, bump m, true)
        else ({ c.setR rdn r with pc := next }, bump (m.emit (.reg rdn r)), true)
      | 1 =>   -- CMP high (flags only)
        let r := rRd rdn - rmV
        ({ setSubFlags c (rRd rdn) rmV r with pc := next }, bump m, true)
      | 2 =>   -- MOV high (no flags)
        if rdn == 15 then
          if c.haltOnSelfBranch && rmV &&& ~~~1 == pc then
            ({ c with halted := true, blocked := true }, bump (m.emit (.note "frontier")), false)
          else ({ c with pc := rmV &&& ~~~1, tbit := rmV &&& 1 == 1 }, bump m, true)
        else ({ c.setR rdn rmV with pc := next }, bump (m.emit (.reg rdn rmV)), true)
      | _ =>   -- BX / BLX register
        let isBLX := (w >>> 7) &&& 1 == 1
        if c.haltOnSelfBranch && rmV &&& ~~~1 == pc then
          ({ c with halted := true, blocked := true }, bump (m.emit (.note "frontier")), false)
        else
          let c' := if isBLX then c.setR 14 (next ||| 1) else c
          ({ c' with pc := rmV &&& ~~~1, tbit := rmV &&& 1 == 1 },
           bump (m.emit (.note (if isBLX then "blx" else "bx"))), true)
    -- ── 01001: LDR (literal / PC-relative) ───────────────────────────────────
    else if (w >>> 11) == 0b01001 then
      let rd   := (w >>> 8) &&& 0x7
      let addr := pcR + BitVec.ofNat 32 ((w &&& 0xff) * 4)
      let (res, m) := c.memRead m addr 32
      match res with
      | .error _ => takeDabt c m
      | .ok v => ({ c.setR rd v with pc := next }, bump (m.emit (.reg rd v)), true)
    -- ── 0101: load/store register offset ─────────────────────────────────────
    else if (w >>> 12) == 0b0101 then
      let op   := (w >>> 9) &&& 0x7
      let addr := c.regs.getD ((w >>> 3) &&& 0x7) 0 + c.regs.getD ((w >>> 6) &&& 0x7) 0
      let rt   := w &&& 0x7
      match op with
      | 0 => let (_,m) := c.memWrite m addr (c.regs.getD rt 0) 32
             ({ c with pc := next }, bump m, true)
      | 1 => let (_,m) := c.memWrite m addr (c.regs.getD rt 0) 16
             ({ c with pc := next }, bump m, true)
      | 2 => let (_,m) := c.memWrite m addr (c.regs.getD rt 0) 8
             ({ c with pc := next }, bump m, true)
      | 3 => let (res,m) := c.memRead m addr 8     -- LDRSB
             match res with
             | .error _ => takeDabt c m
             | .ok v => let v' : Word := (BitVec.ofNat 8 v.toNat).signExtend 32
                        ({ c.setR rt v' with pc := next }, bump (m.emit (.reg rt v')), true)
      | 4 => let (res,m) := c.memRead m addr 32
             match res with
             | .error _ => takeDabt c m
             | .ok v => ({ c.setR rt v with pc := next }, bump (m.emit (.reg rt v)), true)
      | 5 => let (res,m) := c.memRead m addr 16
             match res with
             | .error _ => takeDabt c m
             | .ok v => ({ c.setR rt v with pc := next }, bump (m.emit (.reg rt v)), true)
      | 6 => let (res,m) := c.memRead m addr 8
             match res with
             | .error _ => takeDabt c m
             | .ok v => ({ c.setR rt v with pc := next }, bump (m.emit (.reg rt v)), true)
      | _ => let (res,m) := c.memRead m addr 16    -- LDRSH
             match res with
             | .error _ => takeDabt c m
             | .ok v => let v' : Word := (BitVec.ofNat 16 v.toNat).signExtend 32
                        ({ c.setR rt v' with pc := next }, bump (m.emit (.reg rt v')), true)
    -- ── 011: load/store word/byte immediate offset ────────────────────────────
    else if (w >>> 13) == 0b011 then
      let isLd  := (w >>> 11) &&& 1 == 1
      let isByt := (w >>> 12) &&& 1 == 1
      let imm5  := (w >>> 6) &&& 0x1f
      let rn    := c.regs.getD ((w >>> 3) &&& 0x7) 0
      let rt    := w &&& 0x7
      let addr  := rn + BitVec.ofNat 32 (imm5 * (if isByt then 1 else 4))
      let width := if isByt then 8 else 32
      if isLd then
        let (res,m) := c.memRead m addr width
        match res with
        | .error _ => takeDabt c m
        | .ok v => ({ c.setR rt v with pc := next }, bump (m.emit (.reg rt v)), true)
      else
        let (_,m) := c.memWrite m addr (c.regs.getD rt 0) width
        ({ c with pc := next }, bump m, true)
    -- ── 1000: load/store halfword immediate offset ────────────────────────────
    else if (w >>> 12) == 0b1000 then
      let isLd := (w >>> 11) &&& 1 == 1
      let rn   := c.regs.getD ((w >>> 3) &&& 0x7) 0
      let rt   := w &&& 0x7
      let addr := rn + BitVec.ofNat 32 (((w >>> 6) &&& 0x1f) * 2)
      if isLd then
        let (res,m) := c.memRead m addr 16
        match res with
        | .error _ => takeDabt c m
        | .ok v => ({ c.setR rt v with pc := next }, bump (m.emit (.reg rt v)), true)
      else
        let (_,m) := c.memWrite m addr (c.regs.getD rt 0) 16
        ({ c with pc := next }, bump m, true)
    -- ── 1001: SP-relative load/store ─────────────────────────────────────────
    else if (w >>> 12) == 0b1001 then
      let isLd := (w >>> 11) &&& 1 == 1
      let rd   := (w >>> 8) &&& 0x7
      let addr := c.regs.getD 13 0 + BitVec.ofNat 32 ((w &&& 0xff) * 4)
      if isLd then
        let (res,m) := c.memRead m addr 32
        match res with
        | .error _ => takeDabt c m
        | .ok v => ({ c.setR rd v with pc := next }, bump (m.emit (.reg rd v)), true)
      else
        let (_,m) := c.memWrite m addr (c.regs.getD rd 0) 32
        ({ c with pc := next }, bump m, true)
    -- ── 1010: ADD Rd, PC/SP, #imm ────────────────────────────────────────────
    else if (w >>> 12) == 0b1010 then
      let rd   := (w >>> 8) &&& 0x7
      let base : Word := if (w >>> 11) &&& 1 == 1 then c.regs.getD 13 0 else pcR
      let v    := base + BitVec.ofNat 32 ((w &&& 0xff) * 4)
      ({ c.setR rd v with pc := next }, bump (m.emit (.reg rd v)), true)
    -- ── 1011: miscellaneous ───────────────────────────────────────────────────
    else if (w >>> 12) == 0b1011 then
      let hi4b := (w >>> 8) &&& 0xf
      if hi4b == 0x0 then
        -- ADD/SUB SP, SP, #imm7<<2  (1011 0000 S imm7)
        let isSub := (w >>> 7) &&& 1 == 1
        let imm   := BitVec.ofNat 32 ((w &&& 0x7f) * 4)
        let sp    := c.regs.getD 13 0
        let newSP := if isSub then sp - imm else sp + imm
        ({ c.setR 13 newSP with pc := next }, bump m, true)
      else if hi4b == 0x2 then
        -- ARMv6 SXTH/SXTB/UXTH/UXTB  (1011 0010 op rm rd)
        let op := (w >>> 6) &&& 0x3
        let rm := c.regs.getD ((w >>> 3) &&& 0x7) 0
        let rd := w &&& 0x7
        let v : Word := match op with
          | 0 => (BitVec.ofNat 16 rm.toNat).signExtend 32
          | 1 => (BitVec.ofNat 8  rm.toNat).signExtend 32
          | 2 => BitVec.ofNat 32 (rm.toNat &&& 0xffff)
          | _ => BitVec.ofNat 32 (rm.toNat &&& 0xff)
        ({ c.setR rd v with pc := next }, bump (m.emit (.reg rd v)), true)
      else if (w >>> 9) &&& 0x7 == 0b010 then
        -- PUSH  (1011 0 R 10 rlist)
        let rlist  := w &&& 0xff
        let regs   := (List.range 8).filter (fun i => (rlist >>> i) &&& 1 == 1)
                      ++ (if (w >>> 8) &&& 1 == 1 then [14] else [])
        let sp     := c.regs.getD 13 0
        let newSP  := sp - BitVec.ofNat 32 (regs.length * 4)
        let m := Id.run do
          let mut m := m; let mut idx := 0
          for r in regs do
            let (_, m') := c.memWrite m (newSP + BitVec.ofNat 32 (idx * 4)) (c.regs.getD r 0) 32
            m := m'; idx := idx + 1
          return m
        ({ c.setR 13 newSP with pc := next }, bump m, true)
      else if (w >>> 9) &&& 0x7 == 0b110 then
        -- POP   (1011 1 R 10 rlist)
        let rlist  := w &&& 0xff
        let regs   := (List.range 8).filter (fun i => (rlist >>> i) &&& 1 == 1)
        let sp     := c.regs.getD 13 0
        let (c', m) := Id.run do
          let mut c' := c; let mut m := m; let mut idx := 0
          for r in regs do
            let (res, m') := c'.memRead m (sp + BitVec.ofNat 32 (idx * 4)) 32
            m := m'; if let .ok v := res then c' := c'.setR r v; idx := idx + 1
          return (c', m)
        let inclPC := (w >>> 8) &&& 1 == 1
        let n := regs.length + (if inclPC then 1 else 0)
        let newSP := sp + BitVec.ofNat 32 (n * 4)
        if inclPC then
          let (res, m) := c'.memRead m (sp + BitVec.ofNat 32 (regs.length * 4)) 32
          match res with
          | .error _ => takeDabt c' m
          | .ok v =>
            let tgt := v &&& ~~~1
            if c.haltOnSelfBranch && tgt == pc then
              ({ c'.setR 13 newSP with halted := true, blocked := true },
               bump (m.emit (.note "frontier")), false)
            else ({ c'.setR 13 newSP with pc := tgt, tbit := v &&& 1 == 1 }, bump m, true)
        else ({ c'.setR 13 newSP with pc := next }, bump m, true)
      else if (w >>> 8) &&& 0xff == 0xBE then
        -- BKPT  (1011 1110 imm8)
        let (c, m) := takeException c m "undef" next
        (c, bump m, true)
      else if (w >>> 8) &&& 0xff == 0xBA then
        -- ARMv6 REV / REV16 / REVSH  (1011 1010 op rm rd)
        let op := (w >>> 6) &&& 0x3
        let rm := c.regs.getD ((w >>> 3) &&& 0x7) 0
        let rd := w &&& 0x7
        let v : Word := match op with
          | 0 => ((rm &&& 0xff) <<< 24) ||| (((rm >>> 8) &&& 0xff) <<< 16) |||
                 (((rm >>> 16) &&& 0xff) <<< 8) ||| ((rm >>> 24) &&& 0xff)
          | 1 => (((rm >>> 16) &&& 0xff) <<< 24) ||| (((rm >>> 24) &&& 0xff) <<< 16) |||
                 ((rm &&& 0xff) <<< 8) ||| ((rm >>> 8) &&& 0xff)
          | _ => let lo := ((rm &&& 0xff) <<< 8) ||| ((rm >>> 8) &&& 0xff)
                 (BitVec.ofNat 16 lo.toNat).signExtend 32
        ({ c.setR rd v with pc := next }, bump (m.emit (.reg rd v)), true)
      else if hi4b &&& 0b0101 == 0b0001 then
        -- CBZ / CBNZ (1011 {0,1}0{0,1}1 imm5 Rn)
        let isNZ := hi4b &&& 0b1000 != 0   -- bit[11]=1 → CBNZ
        let i    := (w >>> 9) &&& 1          -- extra offset bit
        let imm5 := (w >>> 3) &&& 0x1f
        let rn   := w &&& 0x7
        let rVal := c.regs.getD rn 0
        let off  : Word := BitVec.ofNat 32 ((i <<< 6) ||| (imm5 <<< 1))
        let tgt  := pc + 4 + off
        let taken := if isNZ then rVal != 0 else rVal == 0
        if taken then
          if c.haltOnSelfBranch && tgt == pc then
            ({ c with halted := true, blocked := true }, bump (m.emit (.note "frontier")), false)
          else ({ c with pc := tgt }, bump m, true)
        else ({ c with pc := next }, bump m, true)
      else if (w >>> 8) &&& 0xff == 0xB6 then
        -- CPS / SETEND (10110110 …)
        if (w >>> 5) &&& 1 == 0 then
          -- SETEND: NOP (we don't model endianness state)
          ({ c with pc := next }, bump m, true)
        else
          -- CPS: change IRQ/FIQ enable/disable
          let imod := (w >>> 4) &&& 0x3
          let affI := (w >>> 1) &&& 1 == 1
          let affF := w &&& 1 == 1
          let en := imod == 0b10   -- 10=IE (enable), 11=ID (disable)
          let c' := if affI then { c with iMask := !en } else c
          let c' := if affF then { c' with fMask := !en } else c'
          ({ c' with pc := next }, bump m, true)
      else if (w >>> 8) &&& 0xff == 0xBF then
        -- IT / NOP-class hints (10111111 firstcond mask)
        let firstcond := (w >>> 4) &&& 0xf
        let mask      := w &&& 0xf
        if mask == 0 then
          ({ c with pc := next }, bump m, true)   -- NOP/WFI/WFE/SEV hint → NOP
        else
          ({ c with itState := (firstcond <<< 4) ||| mask, pc := next }, bump m, true)
      else
        ({ c with halted := true }, bump (m.emit (.unsupported pc w "thumb")), false)
    -- ── 1100: STMIA / LDMIA ──────────────────────────────────────────────────
    else if (w >>> 12) == 0b1100 then
      let isLd  := (w >>> 11) &&& 1 == 1
      let rn    := (w >>> 8) &&& 0x7
      let rlist := w &&& 0xff
      let regs  := (List.range 8).filter (fun i => (rlist >>> i) &&& 1 == 1)
      let base  := c.regs.getD rn 0
      if isLd then
        let (c', m) := Id.run do
          let mut c' := c; let mut m := m; let mut idx := 0
          for r in regs do
            let (res, m') := c'.memRead m (base + BitVec.ofNat 32 (idx * 4)) 32
            m := m'; if let .ok v := res then c' := c'.setR r v; idx := idx + 1
          return (c', m)
        -- writeback to Rn unless Rn is in the register list
        let newBase := base + BitVec.ofNat 32 (regs.length * 4)
        let c'' := if regs.any (· == rn) then c' else c'.setR rn newBase
        ({ c'' with pc := next }, bump m, true)
      else
        let m := Id.run do
          let mut m := m; let mut idx := 0
          for r in regs do
            let (_, m') := c.memWrite m (base + BitVec.ofNat 32 (idx * 4)) (c.regs.getD r 0) 32
            m := m'; idx := idx + 1
          return m
        let newBase := base + BitVec.ofNat 32 (regs.length * 4)
        ({ c.setR rn newBase with pc := next }, bump m, true)
    -- ── 1101: conditional branch + SVC ───────────────────────────────────────
    else if (w >>> 12) == 0b1101 then
      let cond := (w >>> 8) &&& 0xf
      if cond == 0xf then    -- SVC
        let (c, m) := takeException c m "swi" next
        (c, bump m, true)
      else if cond == 0xe then   -- UDF (permanently undefined) → UNDEF exception
        let (c', m') := takeException c m "undef" next
        (c', bump m', true)
      else if condHolds c cond then
        let off : Word := (BitVec.ofNat 8 (w &&& 0xff)).signExtend 32
        let tgt := pc + 4 + off * 2
        if c.haltOnSelfBranch && tgt == pc then
          ({ c with halted := true, blocked := true }, bump (m.emit (.note "frontier")), false)
        else ({ c with pc := tgt }, bump m, true)
      else ({ c with pc := next }, bump m, true)
    -- ── 11100: B unconditional ───────────────────────────────────────────────
    else if (w >>> 11) == 0b11100 then
      let off : Word := (BitVec.ofNat 11 (w &&& 0x7ff)).signExtend 32
      let tgt := pc + 4 + off * 2
      if c.haltOnSelfBranch && tgt == pc then
        ({ c with halted := true, blocked := true }, bump (m.emit (.note "frontier")), false)
      else ({ c with pc := tgt }, bump m, true)
    -- ── T32: 32-bit Thumb-2 instructions (hw1[15:11] ∈ {29,30,31}) ──────────
    else if (w >>> 11) >= 0b11101 then
      let (fres2, m) := c.memRead m (pc + 2) 16 (fetch := true)
      match fres2 with
      | .error _ => ({ c with halted := true }, m.emit (.note "fetch_fault"), false)
      | .ok hw2 =>
        let w2 := hw2.toNat &&& 0xffff
        stepThumb32 w w2 c m
    else
      ({ c with halted := true }, bump (m.emit (.unsupported pc w "thumb")), false)

/-- One instruction. Pure and total. -/
def step (c : Cpu) (m : Machine) : Cpu × Machine × Bool :=
  if c.halted then (c, m, false)
  -- interrupt sampling at instruction boundary
  else if c.fiqPending && !c.fMask then
    let (c, m) := takeException { c with fiqPending := false } m "fiq" (c.pc + 4)
    (c, { m with icount := m.icount + 1 }, true)
  else if c.irqPending && !c.iMask then
    let (c, m) := takeException { c with irqPending := false } m "irq" (c.pc + 4)
    (c, { m with icount := m.icount + 1 }, true)
  else if c.tbit then
    -- IT block: skip instruction if condition not met, advance state after execution
    let itMask := c.itState &&& 0xf
    let fc     := c.itState >>> 4
    let nextIT := if itMask &&& 7 == 0 then 0 else (fc <<< 4) ||| ((itMask <<< 1) &&& 0xf)
    if itMask != 0 then
      let cond := if itMask &&& 8 != 0 then fc else fc ^^^ 1
      if !condHolds c cond then
        -- Condition not met: skip instruction (NOP), advance IT state
        -- Must still fetch to determine instruction size (T16 vs T32)
        let (fres, m') := c.memRead m c.pc 16 (fetch := true)
        match fres with
        | .error _ => ({ c with halted := true }, m'.emit (.note "fetch_fault"), false)
        | .ok hw =>
          let hw16 := hw.toNat &&& 0xffff
          let sz : Nat := if hw16 >>> 11 >= 0b11101 then 4 else 2
          let cnt := if sz == 4 then 2 else 1
          ({ c with pc := c.pc + BitVec.ofNat 32 sz, itState := nextIT },
           { m' with icount := m'.icount + cnt }, true)
      else
        -- Condition met: run instruction, then advance IT state in result
        let (c', m', ok) := stepThumb c m
        -- Only advance if the instruction didn't itself modify itState (e.g. IT insn)
        let c'' := if c'.itState == c.itState then { c' with itState := nextIT } else c'
        (c'', m', ok)
    else stepThumb c m  -- not in IT block
  else
    let pc := c.pc
    let (fres, m) := c.memRead m pc 32 (fetch := true)
    match fres with
    | .error _ => ({ c with halted := true }, m.emit (.note "fetch_fault"), false)
    | .ok word =>
      let w := word.toNat
      let cc := (w >>> 28) &&& 0xf
      let m := m.emit (.exec pc (BitVec.ofNat 8 0) (mnem w))
      let bump (m : Machine) : Machine := { m with icount := m.icount + 1 }
      let next : Word := pc + 4
      if cc == 0xF then
        -- Unconditional-instruction space (A5.7): BLX(imm); memory hints &
        -- barriers (PLD/PLI/DSB/DMB/ISB/CLREX) are NOPs; NEON/Advanced-SIMD and
        -- the rest are deferred (fail closed) rather than mis-decoded.
        if (w >>> 25) &&& 0x7 == 0b101 then                  -- BLX immediate (→ Thumb)
          let h := (w >>> 24) &&& 1
          let soff : Word := (BitVec.ofNat 24 (w &&& 0xffffff)).signExtend 32
          let target := pc + 8 + soff * 4 + BitVec.ofNat 32 (h <<< 1)
          ({ (c.setR 14 next) with pc := target &&& ~~~ (1 : Word), tbit := true }, bump m, true)
        else if (w >>> 16) &&& 0xffff == 0xf57f                       -- DSB/DMB/ISB/CLREX → NOP
             || ((w >>> 26) &&& 0x3 == 0b01 && (w >>> 20) &&& 1 == 1 && (w >>> 12) &&& 0xf == 0xf && (w >>> 4) &&& 1 == 0) then  -- PLD/PLI (imm hint) → NOP (bit20=1 excludes NEON ld/st with Vd=15)
          ({ c with pc := next }, bump m, true)
        -- Advanced SIMD (NEON) 3-register, bitwise group (opc 0001, bit4=1):
        -- VAND/VBIC/VORR/VORN (U=0) / VEOR/VBSL/VBIT/VBIF (U=1), selected by sz.
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 0
                && (w >>> 8) &&& 0xf == 1 && (w >>> 4) &&& 1 == 1 then
          let u := (w >>> 24) &&& 1; let sz := (w >>> 20) &&& 3; let q := (w >>> 6) &&& 1 == 1
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let rd (n : Nat) : Nat := if q then c.qReg (n / 2) else (c.dReg n).toNat
          let a := rd dn; let b := rd dm; let od := rd dd
          let r := match u, sz with
            | 0, 0 => Sei.Simd.vand bits a b
            | 0, 1 => Sei.Simd.vbic bits a b
            | 0, 2 => Sei.Simd.vorr bits a b
            | 0, 3 => Sei.Simd.vorn bits a b
            | 1, 0 => Sei.Simd.veor bits a b
            | 1, 1 => Sei.Simd.vbsl bits od a b
            | 1, 2 => Sei.Simd.vbit bits od a b
            | _, _ => Sei.Simd.vbif bits od a b
          let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
          ({ c with pc := next }, bump m, true)
        -- NEON 3-register integer arithmetic: VADD/VSUB (opc 1000, o4=0),
        -- VMLA/VMLS (1001, o4=0), VMUL-int (1001, o4=1). esize = 8<<sz.
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 0
                && (((w >>> 8) &&& 0xf == 0b1000 && (w >>> 4) &&& 1 == 0) || (w >>> 8) &&& 0xf == 0b1001) then
          let u := (w >>> 24) &&& 1; let o4 := (w >>> 4) &&& 1; let opc := (w >>> 8) &&& 0xf
          let q := (w >>> 6) &&& 1 == 1; let esize := 8 <<< ((w >>> 20) &&& 3)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let rd (n : Nat) : Nat := if q then c.qReg (n / 2) else (c.dReg n).toNat
          let a := rd dn; let b := rd dm; let od := rd dd
          if opc == 0b1000 && o4 == 0 then          -- VADD (U=0) / VSUB (U=1)
            let r := if u == 1 then Sei.Simd.vsub bits esize a b else Sei.Simd.vadd bits esize a b
            let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
            ({ c with pc := next }, bump m, true)
          else if opc == 0b1001 && o4 == 1 && u == 0 then   -- VMUL (int)
            let r := Sei.Simd.vmul bits esize a b
            let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
            ({ c with pc := next }, bump m, true)
          else if opc == 0b1001 && o4 == 0 then     -- VMLA (U=0) / VMLS (U=1)
            let r := if u == 1 then Sei.Simd.vmls bits esize od a b else Sei.Simd.vmla bits esize od a b
            let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
            ({ c with pc := next }, bump m, true)
          else
            let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
            (c, bump m, true)
        -- NEON 3-register compare / min-max / abs-diff / halving. U selects
        -- signed (0) / unsigned (1); s = 1-U for the signed-aware ops.
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 0
                && ((w >>> 8) &&& 0xf == 0b0011 || (w >>> 8) &&& 0xf == 0b0110
                    || (w >>> 8) &&& 0xf == 0b0111
                    || ((w >>> 8) &&& 0xf == 0b0000 && (w >>> 4) &&& 1 == 0)
                    || ((w >>> 8) &&& 0xf == 0b0001 && (w >>> 4) &&& 1 == 0)
                    || ((w >>> 8) &&& 0xf == 0b0010 && (w >>> 4) &&& 1 == 0)
                    || ((w >>> 8) &&& 0xf == 0b1000 && (w >>> 4) &&& 1 == 1)) then
          let u := (w >>> 24) &&& 1; let o4 := (w >>> 4) &&& 1; let opc := (w >>> 8) &&& 0xf
          let s := 1 - u
          let q := (w >>> 6) &&& 1 == 1; let esize := 8 <<< ((w >>> 20) &&& 3)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let rd (n : Nat) : Nat := if q then c.qReg (n / 2) else (c.dReg n).toNat
          let a := rd dn; let b := rd dm; let dv := rd dd
          if opc == 0b0111 && o4 == 1 then                                           -- VABA: Dd += |Dn - Dm|
            let absdiff := Sei.Simd.vabd bits esize s a b
            let r := Sei.Simd.vadd bits esize dv absdiff
            let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
            ({ c with pc := next }, bump m, true)
          else
          let r :=
            if opc == 0b0011 then (if o4 == 0 then Sei.Simd.vcgt else Sei.Simd.vcge) bits esize s a b
            else if opc == 0b0110 then (if o4 == 0 then Sei.Simd.vmax else Sei.Simd.vmin) bits esize s a b
            else if opc == 0b0111 then Sei.Simd.vabd bits esize s a b
            else if opc == 0b0000 then Sei.Simd.vhadd bits esize s a b
            else if opc == 0b0001 then Sei.Simd.vrhadd bits esize s a b
            else if opc == 0b0010 then Sei.Simd.vhsub bits esize s a b
            else (if u == 0 then Sei.Simd.vtst else Sei.Simd.vceq) bits esize a b   -- opc 1000 o4=1
          let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
          ({ c with pc := next }, bump m, true)
        -- NEON load/store multiple structures: VLD1-4 / VST1-4. type selects the
        -- register count + interleave factor; VLD1 is contiguous (factor 1), VLD2/3/4
        -- de-interleave. Addressing: Rm=1111 none, 1101 post-inc, else reg offset.
        else if (w >>> 24) &&& 0xff == 0xf4 && (w >>> 23) &&& 1 == 0 && (w >>> 20) &&& 1 == 0
                && ((w >>> 8) &&& 0xf == 0b0111 || (w >>> 8) &&& 0xf == 0b1010
                    || (w >>> 8) &&& 0xf == 0b0110 || (w >>> 8) &&& 0xf == 0b0010
                    || (w >>> 8) &&& 0xf == 0b1000 || (w >>> 8) &&& 0xf == 0b0100
                    || (w >>> 8) &&& 0xf == 0b0000 || (w >>> 8) &&& 0xf == 0b0011) then
          let lBit := (w >>> 21) &&& 1; let rn := (w >>> 16) &&& 0xf; let rm := w &&& 0xf
          let typ := (w >>> 8) &&& 0xf; let esize := 8 <<< ((w >>> 6) &&& 3)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let nregs := if typ == 0b0111 then 1 else if typ == 0b1010 then 2 else if typ == 0b0110 then 3
                       else if typ == 0b0010 || typ == 0b0000 then 4 else if typ == 0b1000 then 2
                       else if typ == 0b0011 then 4 else 3   -- 0b0011: 4 regs stride-2, 32-byte transfer
          let factor := if typ == 0b1000 || typ == 0b0011 then 2
                        else if typ == 0b0100 then 3 else if typ == 0b0000 then 4 else 1
          let align := (w >>> 4) &&& 3
          -- ARM UNDEFINED constraints (else CONSTRAINED UNPREDICTABLE — Unicorn NOPs):
          let undef := rn == 15
            || (factor > 1 && (w >>> 6) &&& 3 == 3)                       -- VLD2/3/4 .64
            || ((typ == 0b0111 || typ == 0b0110 || typ == 0b0100) && (w >>> 5) &&& 1 == 1)
            || ((typ == 0b1010 || typ == 0b1000) && align == 3)
          if undef then
            let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
            (c, bump m, true)
          else
          let base := c.rRead rn
          let dabt (c : Cpu) (m : Machine) := let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" (pc + 8); (c, bump m, true)
          let wb (c : Cpu) : Cpu :=
            if rm == 0b1111 then c
            -- type=0b0011 stride-2: memory span is 4 D-regs wide (32 bytes) even though only 2 D-regs carry data
            else if rm == 0b1101 then c.setR rn (base + BitVec.ofNat 32 (if typ == 0b0011 then 32 else nregs * 8))
            else c.setR rn (base + c.rRead rm)
          if lBit == 1 then                            -- LOAD: read nregs·8 bytes → memval, distribute
            let (mv, m, ok) := Id.run do
              let mut mv := 0; let mut m := m; let mut ok := true
              for i in [0:2*nregs] do
                let (r, m') := m.busRead (base + BitVec.ofNat 32 (4*i)) 32
                m := m'
                match r with | .ok v => mv := mv ||| (v.toNat <<< (i*32)) | _ => ok := false
              return (mv, m, ok)
            let c := Id.run do
              let mut c := c
              if typ == 0b0011 then
                -- stride-2: dd+0 ← even elements, dd+2 ← odd elements, dd+1/dd+3 ← 0
                c := c.setDReg dd (BitVec.ofNat 64 (Sei.Simd.deint 2 esize mv 0))
                c := c.setDReg (dd + 1) (BitVec.ofNat 64 0)
                c := c.setDReg (dd + 2) (BitVec.ofNat 64 (Sei.Simd.deint 2 esize mv 1))
                c := c.setDReg (dd + 3) (BitVec.ofNat 64 0)
              else
                for r in [0:nregs] do
                  let dv := if factor == 1 then (mv >>> (r*64)) &&& 0xffffffffffffffff else Sei.Simd.deint factor esize mv r
                  c := c.setDReg (dd + r) (BitVec.ofNat 64 dv)
              return c
            if ok then ({ (wb c) with pc := next }, bump m, true) else dabt c m
          else                                         -- STORE: build memval, write nregs·8 bytes
            let mv := if typ == 0b0011 then
                        -- stride-2: interleave dd+0 and dd+2
                        Sei.Simd.intl 2 esize #[(c.dReg dd).toNat, (c.dReg (dd + 2)).toNat]
                      else if factor == 1 then Id.run do
                        let mut v := 0
                        for r in [0:nregs] do v := v ||| ((c.dReg (dd + r)).toNat <<< (r*64))
                        return v
                      else Sei.Simd.intl factor esize (Id.run do
                        let mut a : Array Nat := #[]
                        for r in [0:nregs] do a := a.push (c.dReg (dd + r)).toNat
                        return a)
            let (m, ok) := Id.run do
              let mut m := m; let mut ok := true
              for i in [0:2*nregs] do
                let (r, m') := m.busWrite (base + BitVec.ofNat 32 (4*i)) (BitVec.ofNat 32 ((mv >>> (i*32)) % 4294967296)) 32
                m := m'
                match r with | .ok _ => pure () | _ => ok := false
              return (m, ok)
            if ok then ({ (wb c) with pc := next }, bump m, true) else dabt c m
        -- NEON single-element load/store (VLDn/VSTn to/from one lane, or VLDn all-lanes).
        -- bit23=1 distinguishes from multiple-structure (bit23=0). bits[7:4]=0 ↔ lane=0.
        -- bits[11:10]=11 → all-lanes VLD; bits[7:6] gives esize for that form.
        -- For one-lane: bits[11:10]=size(00=8,01=16,10=32), bits[9:8]=nregs-1.
        else if (w >>> 24) &&& 0xff == 0xf4 && (w >>> 23) &&& 1 == 1
                && (w >>> 4) &&& 0xf == 0 && (w >>> 16) &&& 0xf != 0xf then
          let lBit := (w >>> 21) &&& 1    -- 1=load, 0=store
          let rn := (w >>> 16) &&& 0xf
          let rm := w &&& 0xf
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let allLanes := (w >>> 10) &&& 0x3 == 0x3   -- bits[11:10]=11 → VLDn all-lanes
          let esize_b :=    -- element size in bytes
            if allLanes then 1 <<< ((w >>> 6) &&& 0x3)    -- bits[7:6] for all-lanes esize
            else 1 <<< ((w >>> 10) &&& 0x3)               -- bits[11:10] for one-lane esize
          let nregs := ((w >>> 8) &&& 0x3) + 1
          let base := c.rRead rn
          let dabt2 (c : Cpu) (m : Machine) := let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" (pc + 8); (c, bump m, true)
          let wb2 (c : Cpu) : Cpu :=
            if rm == 0xf then c
            else if rm == 0xd then c.setR rn (base + BitVec.ofNat 32 (nregs * esize_b))
            else c.setR rn (base + c.rRead rm)
          if lBit == 0 then    -- STORE: write element lane 0 from each D-reg to memory
            let (m2, ok) := Id.run do
              let mut m2 := m; let mut ok := true
              for i in [0:nregs] do
                let dv := (c.dReg (dd + i)).toNat
                let ev := dv &&& ((1 <<< (esize_b * 8)) - 1)
                let addr := base + BitVec.ofNat 32 (i * esize_b)
                let (r, m') := c.memWrite m2 addr (BitVec.ofNat 32 ev) (esize_b * 8)
                m2 := m'
                match r with | .ok _ => pure () | _ => ok := false
              return (m2, ok)
            if ok then ({ (wb2 c) with pc := next }, bump m2, true) else dabt2 c m
          else if allLanes then   -- VLDn all-lanes: load one element, replicate to all lanes
            let (c2, m2, ok) := Id.run do
              let mut c2 := c; let mut m2 := m; let mut ok := true
              for i in [0:nregs] do
                let addr := base + BitVec.ofNat 32 (i * esize_b)
                let (r, m') := c.memRead m2 addr (esize_b * 8)
                m2 := m'
                match r with
                | .ok v =>
                  let ev := v.toNat &&& ((1 <<< (esize_b * 8)) - 1)
                  let nlanes := 64 / (esize_b * 8)
                  let newDv := Id.run do
                    let mut r := 0
                    for j in [0:nlanes] do r := r ||| (ev <<< (j * esize_b * 8))
                    return r
                  c2 := c2.setDReg (dd + i) (BitVec.ofNat 64 newDv)
                | _ => ok := false
              return (c2, m2, ok)
            if ok then ({ (wb2 c2) with pc := next }, bump m2, true) else dabt2 c m
          else   -- VLDn one-lane: load element into lane 0 of each D-reg
            let (c2, m2, ok) := Id.run do
              let mut c2 := c; let mut m2 := m; let mut ok := true
              for i in [0:nregs] do
                let addr := base + BitVec.ofNat 32 (i * esize_b)
                let (r, m') := c.memRead m2 addr (esize_b * 8)
                m2 := m'
                match r with
                | .ok v =>
                  let dv := (c2.dReg (dd + i)).toNat
                  let lmask := (1 <<< (esize_b * 8)) - 1
                  let newDv := (dv &&& (Sei.Simd.mask 64 ^^^ lmask)) ||| (v.toNat &&& lmask)
                  c2 := c2.setDReg (dd + i) (BitVec.ofNat 64 newDv)
                | _ => ok := false
              return (c2, m2, ok)
            if ok then ({ (wb2 c2) with pc := next }, bump m2, true) else dabt2 c m
        -- NEON 3-register saturating add/sub: VQADD (opc 0000) / VQSUB (opc 0010),
        -- o4=1. Operands Vn/Vm; U = unsigned.
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 0 && (w >>> 4) &&& 1 == 1
                && ((w >>> 8) &&& 0xf == 0b0000 || (w >>> 8) &&& 0xf == 0b0010) then
          let u := (w >>> 24) &&& 1; let q := (w >>> 6) &&& 1 == 1; let esize := 8 <<< ((w >>> 20) &&& 3)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let rd (n : Nat) : Nat := if q then c.qReg (n / 2) else (c.dReg n).toNat
          let r := if (w >>> 8) &&& 0xf == 0b0000 then Sei.Simd.vqadd bits esize (1 - u) (rd dn) (rd dm)
                   else Sei.Simd.vqsub bits esize (1 - u) (rd dn) (rd dm)
          let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
          ({ c with pc := next }, bump m, true)
        -- NEON register variable shift: VSHL/VRSHL (o4=0) / VQSHL/VQRSHL (o4=1),
        -- opc 0100/0101. Value is Vm, shift amount is Vn; U = unsigned.
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 0
                && ((w >>> 8) &&& 0xf == 0b0100 || (w >>> 8) &&& 0xf == 0b0101) then
          let u := (w >>> 24) &&& 1; let o4 := (w >>> 4) &&& 1
          let rnd := if (w >>> 8) &&& 0xf == 0b0101 then 1 else 0
          let q := (w >>> 6) &&& 1 == 1; let esize := 8 <<< ((w >>> 20) &&& 3)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let rd (n : Nat) : Nat := if q then c.qReg (n / 2) else (c.dReg n).toNat
          let r := if o4 == 1 then Sei.Simd.vqshlReg bits esize (1 - u) rnd (rd dm) (rd dn)
                   else Sei.Simd.vshlReg bits esize (1 - u) rnd (rd dm) (rd dn)
          let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
          ({ c with pc := next }, bump m, true)
        -- NEON two-register shift by immediate (narrowing): VSHRN/VRSHRN (opc 1000),
        -- VQSHRN.s/u/VQRSHRN.s/u (opc 1001), VQSHRUN/VQRSHRUN (opc 1000 U=1).
        -- Input: Qm (128-bit); output: Dd (64-bit).  sh = esize - imm (the shift amount).
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 1 && (w >>> 7) &&& 1 == 0
                && ((w >>> 19) &&& 0x7 != 0)   -- L=0; imm6[5:3]≠0 excludes modify-immediate space
                && (w >>> 4) &&& 1 == 1
                && ((w >>> 8) &&& 0xf == 0b1000 || (w >>> 8) &&& 0xf == 0b1001) then
          let u := (w >>> 24) &&& 1; let opc := (w >>> 8) &&& 0xf
          let imm6 := (w >>> 16) &&& 0x3f
          let esize := if imm6 &&& 0x20 != 0 then 32 else if imm6 &&& 0x10 != 0 then 16 else 8
          let sh := esize - (imm6 &&& (esize - 1))   -- ARM: shift = esize - imm (where imm ∈ [1,esize])
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let a := c.qReg (dm / 2)   -- input is Q (128-bit)
          let r :=
            if opc == 0b1000 && u == 0 then Sei.Simd.vshrn esize 0 sh a   -- VSHRN
            else if opc == 0b1000 then Sei.Simd.vqmovn esize 1 sh 0 a     -- VQSHRUN (U=1, signed→unsigned)
            else if u == 0 then Sei.Simd.vqmovn esize 0 sh 0 a            -- VQSHRN.s
            else Sei.Simd.vqmovn esize 2 sh 0 a                           -- VQSHRN.u (unsigned→unsigned)
          ({ (c.setDReg dd (BitVec.ofNat 64 r)) with pc := next }, bump m, true)
        -- NEON two-register shift by immediate: VSHR/VSRA/VRSHR/VRSRA (right, opc
        -- 0000-0011), VSRI (0100), VSHL-imm/VSLI (0101). Narrowing/saturating
        -- (opc ≥ 0110) deferred. esize/shift from L:imm6.
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 1
                && ((w >>> 19) &&& 0x7 != 0 || (w >>> 7) &&& 1 == 1)   -- imm6[5:3]≠0 or L=1 (esize 64); excludes modify-immediate
                && (w >>> 4) &&& 1 == 1 && (w >>> 8) &&& 0xf ≤ 0b0111 then
          let u := (w >>> 24) &&& 1; let opc := (w >>> 8) &&& 0xf
          let imm6 := (w >>> 16) &&& 0x3f; let lbit := (w >>> 7) &&& 1
          let xv := (lbit <<< 6) ||| imm6
          let esize := if lbit == 1 then 64 else if imm6 &&& 0x20 != 0 then 32
                       else if imm6 &&& 0x10 != 0 then 16 else 8
          let q := (w >>> 6) &&& 1 == 1
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let rd (n : Nat) : Nat := if q then c.qReg (n / 2) else (c.dReg n).toNat
          let a := rd dm; let od := rd dd; let s := 1 - u
          let r :=
            if opc == 0b0000 then Sei.Simd.vshrImm bits esize s 0 (2*esize - xv) a
            else if opc == 0b0001 then Sei.Simd.vsraImm bits esize s 0 (2*esize - xv) od a
            else if opc == 0b0010 then Sei.Simd.vshrImm bits esize s 1 (2*esize - xv) a
            else if opc == 0b0011 then Sei.Simd.vsraImm bits esize s 1 (2*esize - xv) od a
            else if opc == 0b0100 then Sei.Simd.vsri bits esize (2*esize - xv) od a
            else if opc == 0b0101 then (if u == 1 then Sei.Simd.vsli bits esize (xv - esize) od a   -- VSLI
                                        else Sei.Simd.vshlImm bits esize (xv - esize) a)            -- VSHL imm
            else if opc == 0b0111 then Sei.Simd.vqshlImm bits esize (1 - u) 0 (xv - esize) a        -- VQSHL
            else Sei.Simd.vqshlImm bits esize 0 1 (xv - esize) a                                    -- VQSHLU (opc 0110)
          let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
          ({ c with pc := next }, bump m, true)
        -- NEON VTBL/VTBX: byte table lookup over Dn..Dn+len, indexed by Dm. op=VTBX.
        else if (w >>> 24) &&& 0xff == 0xf3 && (w >>> 20) &&& 0xf == 0xb
                && (w >>> 10) &&& 0x3 == 0b10 && (w >>> 4) &&& 1 == 0 then
          let len := (w >>> 8) &&& 0x3; let ext := (w >>> 6) &&& 1 == 1
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let table := Id.run do
            let mut t := 0
            for i in [0:len+1] do t := t ||| ((c.dReg (dn + i)).toNat <<< (i*64))
            return t
          let r := Sei.Simd.vtbl len (c.dReg dd).toNat (c.dReg dm).toNat table ext
          ({ (c.setDReg dd (BitVec.ofNat 64 r)) with pc := next }, bump m, true)
        -- NEON saturating doubling multiply high: VQDMULH (U=0) / VQRDMULH (U=1),
        -- opc 1011, o4=0.
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 0 && (w >>> 4) &&& 1 == 0
                && (w >>> 8) &&& 0xf == 0b1011 then
          let u := (w >>> 24) &&& 1; let q := (w >>> 6) &&& 1 == 1; let esize := 8 <<< ((w >>> 20) &&& 3)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let rd (n : Nat) : Nat := if q then c.qReg (n / 2) else (c.dReg n).toNat
          let r := Sei.Simd.vqdmulh bits esize u (rd dn) (rd dm)
          ({ (if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)) with pc := next }, bump m, true)
        -- NEON 2-reg-misc extras: VCVT.F32↔int (A=11 opc2 11xx), compare-with-zero
        -- (A=01, op=bits[9:7], F=bit10), and VTBL/VTBX (bits[11:10]=10).
        else if (w >>> 24) &&& 0xff == 0xf3 && (w >>> 20) &&& 0xf == 0xb && (w >>> 11) &&& 1 == 0
                && (w >>> 4) &&& 1 == 0
                && (((w >>> 16) &&& 0x3 == 3 && (w >>> 9) &&& 0x3 == 0x3)        -- VCVT (opc2 11xx)
                    || ((w >>> 16) &&& 0x3 == 1 && (w >>> 7) &&& 0x7 ≤ 4)) then  -- compare-zero
          let q := (w >>> 6) &&& 1 == 1; let esize := 8 <<< ((w >>> 18) &&& 3)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let x := if q then c.qReg (dm / 2) else (c.dReg dm).toNat
          let r :=
            if (w >>> 16) &&& 0x3 == 3 then                       -- VCVT (opc2 bits[9:8] pick direction)
              if (w >>> 8) &&& 1 == 0 then Sei.Simd.vcvtFromInt bits (1 - ((w >>> 7) &&& 1)) x  -- f32.s32/u32
              else Sei.Simd.vcvtToInt bits (1 - ((w >>> 7) &&& 1)) x                            -- s32/u32.f32
            else if (w >>> 10) &&& 1 == 1 then Sei.Simd.vfcmpz bits x ((w >>> 7) &&& 0x7)        -- FP compare-zero
            else Sei.Simd.vcmpz bits esize x ((w >>> 7) &&& 0x7)                                 -- int compare-zero
          ({ (if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)) with pc := next }, bump m, true)
        -- NEON integer pairwise (D-register only): VPMAX/VPMIN (opc 1010, o4=max/min),
        -- VPADD (opc 1011, o4=1). U selects signed/unsigned for max/min.
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 0 && (w >>> 6) &&& 1 == 0
                && ((w >>> 8) &&& 0xf == 0b1010 || ((w >>> 8) &&& 0xf == 0b1011 && (w >>> 4) &&& 1 == 1)) then
          let u := (w >>> 24) &&& 1; let o4 := (w >>> 4) &&& 1; let esize := 8 <<< ((w >>> 20) &&& 3)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let a := (c.dReg dn).toNat; let b := (c.dReg dm).toNat
          let r := if (w >>> 8) &&& 0xf == 0b1011 then Sei.Simd.vpadd esize a b
                   else if o4 == 0 then Sei.Simd.vpmax esize (1 - u) a b
                   else Sei.Simd.vpmin esize (1 - u) a b
          ({ (c.setDReg dd (BitVec.ofNat 64 r)) with pc := next }, bump m, true)
        -- NEON 3-register floating-point (Standard mode). opc 1100-1111 select the
        -- FP ops via U / o4 / sz(bit21). Pairwise (VPADD/VPMAX/VPMIN.F32) deferred.
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 0 && (w >>> 8) &&& 0xf ≥ 0b1100 then
          let u := (w >>> 24) &&& 1; let o4 := (w >>> 4) &&& 1; let opc := (w >>> 8) &&& 0xf
          let sz1 := (w >>> 21) &&& 1; let q := (w >>> 6) &&& 1 == 1
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let rd (n : Nat) : Nat := if q then c.qReg (n / 2) else (c.dReg n).toNat
          let a := rd dn; let b := rd dm; let od := rd dd
          let ro : Option Nat :=
            if opc == 0b1100 && o4 == 1 then some ((if sz1 == 0 then Sei.Simd.vfFma else Sei.Simd.vfFms) bits od a b)
            else if opc == 0b1101 && o4 == 0 && u == 0 then some ((if sz1 == 0 then Sei.Simd.vfAdd else Sei.Simd.vfSub) bits a b)
            else if opc == 0b1101 && o4 == 1 && u == 0 then some ((if sz1 == 0 then Sei.Simd.vfMla else Sei.Simd.vfMls) bits od a b)
            else if opc == 0b1101 && o4 == 1 && u == 1 then some (Sei.Simd.vfMul bits a b)
            else if opc == 0b1101 && o4 == 0 && u == 1 && sz1 == 1 then some (Sei.Simd.vfAbd bits a b)
            else if opc == 0b1110 && o4 == 0 && u == 0 then some (Sei.Simd.vfCeq bits a b)
            else if opc == 0b1110 && o4 == 0 && u == 1 then some ((if sz1 == 0 then Sei.Simd.vfCge else Sei.Simd.vfCgt) bits a b)
            else if opc == 0b1110 && o4 == 1 && u == 1 then some ((if sz1 == 0 then Sei.Simd.vfAcge else Sei.Simd.vfAcgt) bits a b)
            else if opc == 0b1111 && o4 == 0 && u == 0 then some ((if sz1 == 0 then Sei.Simd.vfMax else Sei.Simd.vfMin) bits a b)
            else if opc == 0b1111 && o4 == 1 && u == 0 then some ((if sz1 == 0 then Sei.Simd.vfRecps else Sei.Simd.vfRsqrts) bits a b)
            else if opc == 0b1101 && o4 == 0 && u == 1 && sz1 == 0 && ¬ q then some (Sei.Simd.vpaddF a b)
            else if opc == 0b1111 && o4 == 0 && u == 1 && ¬ q then some (if sz1 == 0 then Sei.Simd.vpmaxF a b else Sei.Simd.vpminF a b)
            else none
          match ro with
          | some r => ({ (if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)) with pc := next }, bump m, true)
          | none => let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next; (c, bump m, true)
        -- NEON two-register miscellaneous: VREV/VCLS/VCLZ/VCNT/VMVN (A=00), VABS/
        -- VNEG int (A=01), VSWP/VTRN/VUZP/VZIP (A=10, write both Dd and Dm).
        else if (w >>> 24) &&& 0xff == 0xf3 && (w >>> 20) &&& 0xf == 0xb && (w >>> 4) &&& 1 == 0
                && (w >>> 11) &&& 1 == 0 && (w >>> 16) &&& 0x3 ≤ 2
                && (((w >>> 16) &&& 0x3 == 0 && ((w >>> 7) &&& 0xf ≤ 2 || (4 ≤ (w >>> 7) &&& 0xf && (w >>> 7) &&& 0xf ≤ 0xf)))
                    || ((w >>> 16) &&& 0x3 == 1 && ((w >>> 7) &&& 0xf == 6 || (w >>> 7) &&& 0xf == 7
                          || (w >>> 7) &&& 0xf == 14 || (w >>> 7) &&& 0xf == 15))
                    || ((w >>> 16) &&& 0x3 == 2 && (w >>> 7) &&& 0xf ≤ 6)) then
          let av := (w >>> 16) &&& 0x3; let opc2 := (w >>> 7) &&& 0xf; let q := (w >>> 6) &&& 1 == 1
          let esize := 8 <<< ((w >>> 18) &&& 3)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let rd (n : Nat) : Nat := if q then c.qReg (n / 2) else (c.dReg n).toNat
          let wr (cc : Cpu) (n v : Nat) : Cpu := if q then cc.setQReg (n / 2) v else cc.setDReg n (BitVec.ofNat 64 v)
          let x := rd dm
          if av == 2 && opc2 == 4 && ¬ q then         -- VMOVN: narrow Qm → Dd
            ({ (c.setDReg dd (BitVec.ofNat 64 (Sei.Simd.vmovn esize (c.qReg (dm / 2))))) with pc := next }, bump m, true)
          else if av == 2 && opc2 == 4 && q then       -- VQMOVUN: signed Q → unsigned D saturated
            ({ (c.setDReg dd (BitVec.ofNat 64 (Sei.Simd.vqmovn esize 1 0 0 (c.qReg (dm / 2))))) with pc := next }, bump m, true)
          else if av == 2 && opc2 == 5 && ¬ q then    -- VQMOVN.s: signed Q → signed D
            ({ (c.setDReg dd (BitVec.ofNat 64 (Sei.Simd.vqmovn esize 0 0 0 (c.qReg (dm / 2))))) with pc := next }, bump m, true)
          else if av == 2 && opc2 == 5 && q then       -- VQMOVN.u: unsigned Q → unsigned D
            ({ (c.setDReg dd (BitVec.ofNat 64 (Sei.Simd.vqmovn esize 2 0 0 (c.qReg (dm / 2))))) with pc := next }, bump m, true)
          else if av == 2 && opc2 == 6 then             -- VSHLL_A2: shift each lane left by esize bits
            let r := Sei.Simd.vshll esize 0 esize (c.dReg dm).toNat
            ({ (c.setQReg (dd / 2) r) with pc := next }, bump m, true)
          else if av == 2 then                         -- VSWP/VTRN/VUZP/VZIP (two outputs)
            let dv := rd dd
            let (nd, nm) :=
              if opc2 == 0 then (x, dv)                                          -- VSWP
              else if opc2 == 1 then Sei.Simd.vtrn bits esize dv x
              else if opc2 == 2 then Sei.Simd.vuzp bits esize dv x
              else Sei.Simd.vzip bits esize dv x
            ({ (wr (wr c dd nd) dm nm) with pc := next }, bump m, true)
          else
            let r :=
              if av == 1 then (if opc2 == 6 then Sei.Simd.vabsI bits esize x
                               else if opc2 == 7 then Sei.Simd.vnegI bits esize x
                               else if opc2 == 14 then Sei.Simd.vfAbsS bits x else Sei.Simd.vfNegS bits x)
              else if opc2 ≤ 2 then Sei.Simd.vrev bits (64 >>> opc2) esize x   -- VREV64/32/16
              else if opc2 == 4 || opc2 == 5 then Sei.Simd.vpaddl bits esize (1 - (opc2 &&& 1)) x  -- VPADDL s/u
              else if opc2 == 8 then Sei.Simd.vcls bits esize x
              else if opc2 == 9 then Sei.Simd.vclz bits esize x
              else if opc2 == 0xa then Sei.Simd.vcnt bits x
              else if opc2 == 0xb then Sei.Simd.vmvn bits x
              else if opc2 == 12 || opc2 == 13 then Sei.Simd.vpadal bits esize (1 - (opc2 &&& 1)) (rd dd) x  -- VPADAL s/u
              else if opc2 == 14 then Sei.Simd.vqabsI bits esize x
              else Sei.Simd.vqnegI bits esize x                                 -- opc2 15
            ({ (wr c dd r) with pc := next }, bump m, true)
        -- VDUP (scalar): replicate element [index] of Dm across all lanes. imm4
        -- (bits[19:16]) encodes esize + index; Q = bit6.
        else if (w >>> 24) &&& 0xff == 0xf3 && (w >>> 20) &&& 0xf == 0xb
                && (w >>> 7) &&& 0x1f == 0b11000 && (w >>> 4) &&& 1 == 0 then
          let imm4 := (w >>> 16) &&& 0xf; let q := (w >>> 6) &&& 1 == 1
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let (esize, index) := if imm4 &&& 1 == 1 then (8, imm4 >>> 1)
                                else if imm4 &&& 2 == 2 then (16, imm4 >>> 2) else (32, imm4 >>> 3)
          let bits := if q then 128 else 64
          let elem := Sei.Simd.lane esize (c.dReg dm).toNat index
          let r := Sei.Simd.rep esize (bits / esize) elem
          let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
          ({ c with pc := next }, bump m, true)
        -- VEXT Dd,Dn,Dm,#imm — extract a byte window from the Dm:Dn concatenation.
        else if (w >>> 24) &&& 0xff == 0xf2 && (w >>> 23) &&& 1 == 1 && (w >>> 20) &&& 0x3 == 0x3
                && (w >>> 4) &&& 1 == 0 then
          let q := (w >>> 6) &&& 1 == 1; let imm4 := (w >>> 8) &&& 0xf
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let bits := if q then 128 else 64
          let rd (n : Nat) : Nat := if q then c.qReg (n / 2) else (c.dReg n).toNat
          let cat := rd dn ||| (rd dm <<< bits)               -- Dm:Dn, shift right by imm bytes
          let r := (cat >>> (imm4 * 8)) &&& Sei.Simd.mask bits
          let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
          ({ c with pc := next }, bump m, true)
        -- NEON VSHLL / VMOVL (widen + shift-left, 2-reg-shift opc 1010). esize is
        -- the input size from L:imm6; shift = x − esize (VMOVL = shift 0).
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 1 && (w >>> 4) &&& 1 == 1
                && (w >>> 8) &&& 0xf == 0b1010
                && ((w >>> 19) &&& 0x7 != 0 || (w >>> 7) &&& 1 == 1) then
          let u := (w >>> 24) &&& 1; let imm6 := (w >>> 16) &&& 0x3f; let lbit := (w >>> 7) &&& 1
          let xv := (lbit <<< 6) ||| imm6
          let esize := if lbit == 1 then 64 else if imm6 &&& 0x20 != 0 then 32
                       else if imm6 &&& 0x10 != 0 then 16 else 8
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let r := Sei.Simd.vshll esize (1 - u) (xv - esize) (c.dReg dm).toNat
          ({ (c.setQReg (dd / 2) r) with pc := next }, bump m, true)
        -- NEON 3-register different lengths (widening): VADDL/VSUBL/VMULL/VABDL
        -- (D×D→Q), VADDW/VSUBW (Q×D→Q), VMLAL/VMLSL/VABAL (accumulate). bit4=0,
        -- bit6=0, size≠11. VQDMULL/VQDMLAL/VQDMLSL (opc 1101/1001/1011).
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 1 && (w >>> 4) &&& 1 == 0
                && (w >>> 6) &&& 1 == 0 && (w >>> 20) &&& 0x3 != 0x3 then
          let u := (w >>> 24) &&& 1; let opc := (w >>> 8) &&& 0xf; let s := 1 - u
          let esize := 8 <<< ((w >>> 20) &&& 3)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let a := (c.dReg dn).toNat; let b := (c.dReg dm).toNat
          let qa := c.qReg (dn / 2); let od := c.qReg (dd / 2)
          if opc == 0b0100 || opc == 0b0110 then        -- VADDHN/VSUBHN (narrow → D)
            let r := Sei.Simd.vaddhn esize qa (c.qReg (dm / 2)) (opc == 0b0110) (u == 1)
            ({ (c.setDReg dd (BitVec.ofNat 64 r)) with pc := next }, bump m, true)
          else
          let ro : Option Nat :=
            if opc == 0b0000 then some (Sei.Simd.vaddl esize s a b)
            else if opc == 0b0010 then some (Sei.Simd.vsubl esize s a b)
            else if opc == 0b1100 then some (Sei.Simd.vmull esize s a b)
            else if opc == 0b0111 then some (Sei.Simd.vabdl esize s a b)
            else if opc == 0b0001 then some (Sei.Simd.widenW esize s qa b false)
            else if opc == 0b0011 then some (Sei.Simd.widenW esize s qa b true)
            else if opc == 0b1000 then some (Sei.Simd.widenAcc esize s od a b false false)
            else if opc == 0b1010 then some (Sei.Simd.widenAcc esize s od a b true false)
            else if opc == 0b0101 then some (Sei.Simd.widenAcc esize s od a b false true)
            else if opc == 0b1101 then some (Sei.Simd.vqdmull esize s a b)                  -- VQDMULL
            else if opc == 0b1001 then some (Sei.Simd.vqdmlacc esize s 0 od a b)             -- VQDMLAL
            else if opc == 0b1011 then some (Sei.Simd.vqdmlacc esize s 1 od a b)            -- VQDMLSL
            else none
          match ro with
          | some r => ({ (c.setQReg (dd / 2) r) with pc := next }, bump m, true)
          | none => let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next; (c, bump m, true)
        -- NEON one-register modified immediate: VMOV.i / VMVN.i / VORR.i / VBIC.i.
        -- cmode[0]=1 with cmode[3:1]<0b110 → VORR.i (op=0) / VBIC.i (op=1): read-modify-write.
        -- All others (cmode[0]=0, or cmode[3:1]=0b110/111) → VMOV / VMVN / F32 / i64.
        else if (w >>> 25) &&& 0x7 == 1 && (w >>> 23) &&& 1 == 1 && (w >>> 19) &&& 0x7 == 0
                && (w >>> 4) &&& 1 == 1 then
          let cmode := (w >>> 8) &&& 0xf; let op := (w >>> 5) &&& 1; let q := (w >>> 6) &&& 1 == 1
          let imm8 := (((w >>> 24) &&& 1) <<< 7) ||| (((w >>> 16) &&& 0x7) <<< 4) ||| (w &&& 0xf)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let isVorrVbic := cmode &&& 1 == 1 && cmode >>> 1 < 0b110
          let c :=
            if isVorrVbic then
              let imm64 := Sei.Simd.advExpand 0 cmode imm8
              if q then
                let cur := c.qReg (dd / 2)
                let imm128 := imm64 ||| (imm64 <<< 64)
                let r := if op == 0 then cur ||| imm128 else cur &&& (Sei.Simd.mask 128 ^^^ imm128)
                c.setQReg (dd / 2) r
              else
                let cur := (c.dReg dd).toNat
                let r := if op == 0 then cur ||| imm64 else cur &&& (Sei.Simd.mask 64 ^^^ imm64)
                c.setDReg dd (BitVec.ofNat 64 r)
            else
              let v := Sei.Simd.vmovImm op cmode imm8
              if q then c.setQReg (dd / 2) (v + v * 18446744073709551616) else c.setDReg dd (BitVec.ofNat 64 v)
          ({ c with pc := next }, bump m, true)
        -- SETEND / CPS (bits[27:20]=0x10) → NOP (no effect on tracked state)
        else if (w >>> 20) &&& 0xff == 0x10 then
          ({ c with pc := next }, bump m, true)
        else
          let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
          (c, bump m, true)
      else if !condHolds c cc then ({ c with pc := next }, bump m, true)
      else
        let top := (w >>> 25) &&& 0x7
        -- BX rm (interworking): T-bit ← rm[0], branch to rm & ~1 (B4 Thumb entry)
        if (w >>> 4) &&& 0xffffff == 0x12fff1 then
          let tgt := c.rRead (w &&& 0xf)
          let toThumb := tgt &&& 1 == 1
          let dest := tgt &&& ~~~ (1 : Word)
          if c.haltOnSelfBranch && dest == pc then
            ({ c with halted := true, blocked := true }, bump (m.emit (.note "frontier")), false)
          else
            ({ c with pc := dest, tbit := toThumb },
             bump (m.emit (.note (if toThumb then "bx_thumb" else "bx_arm"))), true)
        -- Branch
        else if top == 0b101 then
          let link := (w >>> 24) &&& 1
          let soff : Word := (BitVec.ofNat 24 (w &&& 0xffffff)).signExtend 32
          let r15 := pc + 8
          let target := r15 + soff * 4
          let c := if link == 1 then c.setR 14 next else c
          if target == pc && c.haltOnSelfBranch then
            ({ c with halted := true, blocked := true }, bump (m.emit (.note "frontier")), false)
          else ({ c with pc := target }, bump m, true)
        -- LDM/STM with the S bit (the "^" user-registers / exception-return forms)
        else if top == 0b100 && (w >>> 22) &&& 1 == 1 then
          let lBit' := (w >>> 20) &&& 1
          let list' := w &&& 0xffff
          let hasPC' := (list' >>> 15) &&& 1 == 1
          if lBit' == 1 && hasPC' then
            -- LDM Rn{!}, {rlist, pc}^ : exception return.
            -- Load registers normally, then restore CPSR from SPSR.
            let pBit' := (w >>> 24) &&& 1
            let uBit' := (w >>> 23) &&& 1
            let wBit' := (w >>> 21) &&& 1
            let rn' := (w >>> 16) &&& 0xf
            let regsX := (List.range 16).filter (fun i => (list' >>> i) &&& 1 == 1)
            let n' := regsX.length
            let base' := c.rRead rn'
            let block' : Word := BitVec.ofNat 32 (4 * n')
            let lowest' : Word := if uBit' == 1 then (if pBit' == 1 then base' + 4 else base')
                                  else (if pBit' == 1 then base' - block' else base' - block' + 4)
            let newBase' : Word := if uBit' == 1 then base' + block' else base' - block'
            let stepX := fun (acc : Cpu × Machine × Bool) (ri : Nat × Nat) =>
              let (c, m, okF) := acc
              let (reg, idx) := ri
              let addr := lowest' + BitVec.ofNat 32 (4 * idx)
              match (c.memRead m addr 32) with
              | (.ok v, m) => (c.setR reg v, m, okF)
              | (.error _, m) => (c, m, false)
            let (c, m, okF) := regsX.zipIdx.foldl stepX (c, m, true)
            if !okF then
              let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" (pc + 8)
              (c, bump m, true)
            else
              let rnLoaded' := (list' >>> rn') &&& 1 == 1
              let c := if wBit' == 1 && !rnLoaded' then c.setR rn' newBase' else c
              -- Restore CPSR from SPSR; c.pc already holds the loaded return address.
              let spsr := spsrGet c c.mode
              let c := unpackCpsr c spsr
              (c, bump m, true)
          else
            -- STM^ and LDM^ without PC (user-register forms): deferred
            let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
            (c, bump m, true)
        -- Block data transfer (LDM/STM, incl PUSH/POP)
        else if top == 0b100 then
          let pBit := (w >>> 24) &&& 1
          let uBit := (w >>> 23) &&& 1
          let wBit := (w >>> 21) &&& 1
          let lBit := (w >>> 20) &&& 1
          let rn := (w >>> 16) &&& 0xf
          let list := w &&& 0xffff
          let regs := (List.range 16).filter (fun i => (list >>> i) &&& 1 == 1)  -- low reg → low addr
          let n := regs.length
          let base := c.rRead rn
          let block : Word := BitVec.ofNat 32 (4 * n)
          let lowest : Word := if uBit == 1 then (if pBit == 1 then base + 4 else base)
                               else (if pBit == 1 then base - block else base - block + 4)
          let newBase : Word := if uBit == 1 then base + block else base - block
          let stepReg := fun (acc : Cpu × Machine × Bool) (ri : Nat × Nat) =>
            let (c, m, okF) := acc
            let (reg, idx) := ri
            let addr := lowest + BitVec.ofNat 32 (4 * idx)
            if lBit == 1 then
              match (c.memRead m addr 32) with
              | (.ok v, m) => (c.setR reg v, m, okF)
              | (.error _, m) => (c, m, false)
            else
              match (c.memWrite m addr (c.rRead reg) 32) with
              | (.ok _, m) => (c, m, okF)
              | (.error _, m) => (c, m, false)
          let (c, m, okF) := regs.zipIdx.foldl stepReg (c, m, true)
          -- writeback (suppressed for LDM when the base itself was loaded)
          let rnLoaded := lBit == 1 && (list >>> rn) &&& 1 == 1
          let c := if wBit == 1 && !rnLoaded then c.setR rn newBase else c
          if !okF then
            let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" (pc + 8)
            (c, bump m, true)
          else if lBit == 1 && (list >>> 15) &&& 1 == 1 then     -- POP {pc}: branch + interworking
            let tgt := c.pc
            ({ c with pc := tgt &&& ~~~ (1 : Word), tbit := tgt &&& 1 == 1 }, bump m, true)
          else ({ c with pc := next }, bump m, true)
        -- VFP two-register transfer: VMOV Dm,Rt,Rt2 / Rt,Rt2,Dm (cp11) and the
        -- two-consecutive-S form (cp10). MCRR/MRRC to other coprocessors deferred.
        else if (w >>> 21) &&& 0x7f == 0b1100010 then
          let rt := (w >>> 12) &&& 0xf; let rt2 := (w >>> 16) &&& 0xf
          let toCore := (w >>> 20) &&& 1 == 1
          if (w >>> 8) &&& 0xf == 11 then          -- 64-bit: core pair ↔ Dm
            let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
            if toCore then
              let d := (c.dReg dm).toNat
              ({ ((c.setR rt (BitVec.ofNat 32 (d % 4294967296))).setR rt2 (BitVec.ofNat 32 (d / 4294967296))) with pc := next }, bump m, true)
            else
              ({ (c.setDReg dm ((BitVec.ofNat 64 (c.rRead rt2).toNat <<< 32) ||| BitVec.ofNat 64 (c.rRead rt).toNat)) with pc := next }, bump m, true)
          else if (w >>> 8) &&& 0xf == 10 then      -- core pair ↔ two consecutive S regs
            let sm := ((w &&& 0xf) <<< 1) ||| ((w >>> 5) &&& 1)
            if toCore then
              ({ ((c.setR rt (c.sReg sm)).setR rt2 (c.sReg (sm + 1))) with pc := next }, bump m, true)
            else
              ({ ((c.setSReg sm (c.rRead rt)).setSReg (sm + 1) (c.rRead rt2)) with pc := next }, bump m, true)
          else
            let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
            (c, bump m, true)
        -- VFP load/store (CP10, single precision): VLDR/VSTR + VLDM/VSTM/VPUSH/VPOP
        else if (w >>> 25) &&& 0x7 == 0b110 && (w >>> 8) &&& 0xf == 10 then
          let pBit := (w >>> 24) &&& 1
          let uBit := (w >>> 23) &&& 1
          let wBit := (w >>> 21) &&& 1
          let lBit := (w >>> 20) &&& 1
          let rn := (w >>> 16) &&& 0xf
          let sd := (((w >>> 12) &&& 0xf) <<< 1) ||| ((w >>> 22) &&& 1)   -- Sd = Vd:D
          let imm8 := w &&& 0xff
          let dabt (c : Cpu) (m : Machine) := let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" (pc + 8); (c, bump m, true)
          if pBit == 1 && wBit == 0 then          -- VLDR / VSTR (single reg, imm offset)
            let base := c.rRead rn
            let addr := if uBit == 1 then base + BitVec.ofNat 32 (imm8 <<< 2) else base - BitVec.ofNat 32 (imm8 <<< 2)
            if lBit == 1 then
              match c.memRead m addr 32 with
              | (.ok v, m) => ({ (c.setSReg sd v) with pc := next }, bump m, true)
              | (.error _, m) => dabt c m
            else
              match c.memWrite m addr (c.sReg sd) 32 with
              | (.ok _, m) => ({ c with pc := next }, bump m, true)
              | (.error _, m) => dabt c m
          else                                    -- VLDM / VSTM / VPUSH / VPOP
            let n := imm8                         -- number of single regs
            let block : Word := BitVec.ofNat 32 (4 * n)
            let base := c.rRead rn
            let lowest : Word := if uBit == 1 then base else base - block
            let res := Id.run do
              let mut c := c; let mut m := m; let mut okF := true
              for i in [0:n] do
                let addr := lowest + BitVec.ofNat 32 (4 * i)
                if lBit == 1 then
                  match c.memRead m addr 32 with
                  | (.ok v, m') => m := m'; c := c.setSReg (sd + i) v
                  | (.error _, m') => m := m'; okF := false
                else
                  match c.memWrite m addr (c.sReg (sd + i)) 32 with
                  | (.ok _, m') => m := m'
                  | (.error _, m') => m := m'; okF := false
              return (c, m, okF)
            let (c, m, okF) := res
            let c := if wBit == 1 then c.setR rn (if uBit == 1 then base + block else base - block) else c
            if okF then ({ c with pc := next }, bump m, true) else dabt c m
        -- VFP load/store (CP11, double precision): VLDR/VSTR + VLDM/VSTM/VPUSH/VPOP.64
        else if (w >>> 25) &&& 0x7 == 0b110 && (w >>> 8) &&& 0xf == 11 then
          let pBit := (w >>> 24) &&& 1; let uBit := (w >>> 23) &&& 1
          let wBit := (w >>> 21) &&& 1; let lBit := (w >>> 20) &&& 1
          let rn := (w >>> 16) &&& 0xf
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)   -- Dd = D:Vd
          let imm8 := w &&& 0xff
          let dabt (c : Cpu) (m : Machine) := let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" (pc + 8); (c, bump m, true)
          if pBit == 1 && wBit == 0 then          -- VLDR.64 / VSTR.64
            let base := c.rRead rn
            let addr := if uBit == 1 then base + BitVec.ofNat 32 (imm8 <<< 2) else base - BitVec.ofNat 32 (imm8 <<< 2)
            if lBit == 1 then
              let (r1, m) := c.memRead m addr 32; let (r2, m) := c.memRead m (addr + 4) 32
              match r1, r2 with
              | .ok lo, .ok hi => ({ (c.setDReg dd ((BitVec.ofNat 64 hi.toNat <<< 32) ||| BitVec.ofNat 64 lo.toNat)) with pc := next }, bump m, true)
              | _, _ => dabt c m
            else
              let d := (c.dReg dd).toNat
              let (r1, m) := c.memWrite m addr (BitVec.ofNat 32 (d % 4294967296)) 32
              let (r2, m) := c.memWrite m (addr + 4) (BitVec.ofNat 32 (d / 4294967296)) 32
              match r1, r2 with | .ok _, .ok _ => ({ c with pc := next }, bump m, true) | _, _ => dabt c m
          else                                    -- VLDM/VSTM/VPUSH/VPOP.64 (imm8 = 2 × #D regs)
            let n := imm8 / 2
            let block : Word := BitVec.ofNat 32 (8 * n)
            let base := c.rRead rn
            let lowest : Word := if uBit == 1 then base else base - block
            let res := Id.run do
              let mut c := c; let mut m := m; let mut okF := true
              for i in [0:n] do
                let addr := lowest + BitVec.ofNat 32 (8 * i)
                if lBit == 1 then
                  let (r1, m1) := c.memRead m addr 32; let (r2, m2) := c.memRead m1 (addr + 4) 32
                  m := m2
                  match r1, r2 with
                  | .ok lo, .ok hi => c := c.setDReg (dd + i) ((BitVec.ofNat 64 hi.toNat <<< 32) ||| BitVec.ofNat 64 lo.toNat)
                  | _, _ => okF := false
                else
                  let d := (c.dReg (dd + i)).toNat
                  let (r1, m1) := c.memWrite m addr (BitVec.ofNat 32 (d % 4294967296)) 32
                  let (r2, m2) := c.memWrite m1 (addr + 4) (BitVec.ofNat 32 (d / 4294967296)) 32
                  m := m2
                  match r1, r2 with | .ok _, .ok _ => pure () | _, _ => okF := false
              return (c, m, okF)
            let (c, m, okF) := res
            let c := if wBit == 1 then c.setR rn (if uBit == 1 then base + block else base - block) else c
            if okF then ({ c with pc := next }, bump m, true) else dabt c m
        -- VCVT (int↔float, f32↔f64) — spans CP10/CP11; the int side is always an S
        -- register, the precision side an S (f32) or D (f64) register per sz.
        else if (w >>> 24) &&& 0xf == 0b1110 && (w >>> 4) &&& 1 == 0
                && ((w >>> 8) &&& 0xf == 10 || (w >>> 8) &&& 0xf == 11)
                && (w >>> 20) &&& 0xb == 0xb && (w >>> 6) &&& 1 == 1
                && ((w >>> 16) &&& 0xf == 0b1000 || (w >>> 16) &&& 0xe == 0b1100
                    || (w >>> 16) &&& 0xf == 0b0111) then
          let dbl := (w >>> 8) &&& 1 == 1                 -- sz: double involved
          let opc2 := (w >>> 16) &&& 0xf
          let sd := (((w >>> 12) &&& 0xf) <<< 1) ||| ((w >>> 22) &&& 1)
          let sm := ((w &&& 0xf) <<< 1) ||| ((w >>> 5) &&& 1)
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          if opc2 == 0b1000 then                          -- int → float
            let src := (c.sReg sm).toNat                  -- the integer is in an S reg
            let signed := (w >>> 7) &&& 1 == 1
            if dbl then
              let v := if signed then Sei.Float.i32ToF Sei.Float.Fmt.f64 src else Sei.Float.u32ToF Sei.Float.Fmt.f64 src
              ({ (c.setDReg dd (BitVec.ofNat 64 v)) with pc := next }, bump m, true)
            else
              let v := if signed then Sei.Float.i32ToF Sei.Float.Fmt.f32 src else Sei.Float.u32ToF Sei.Float.Fmt.f32 src
              ({ (c.setSReg sd (BitVec.ofNat 32 v)) with pc := next }, bump m, true)
          else if opc2 == 0b1100 || opc2 == 0b1101 then   -- float → int
            let signed := opc2 == 0b1101
            -- bit7: 1 = VCVT (round toward zero); 0 = VCVTR (round per FPSCR.RMode,
            -- here RNE since FPSCR=0). Round-mode honouring beyond RNE is unmodeled.
            let rne := (w >>> 7) &&& 1 == 0
            let v := if dbl then Sei.Float.fToInt Sei.Float.Fmt.f64 signed rne (c.dReg dm).toNat
                     else Sei.Float.fToInt Sei.Float.Fmt.f32 signed rne (c.sReg sm).toNat
            ({ (c.setSReg sd (BitVec.ofNat 32 v)) with pc := next }, bump m, true)
          else                                            -- opc2 0111: precision conversion
            if dbl then ({ (c.setSReg sd (BitVec.ofNat 32 (Sei.Float.f64ToF32 (c.dReg dm).toNat))) with pc := next }, bump m, true)
            else ({ (c.setDReg dd (BitVec.ofNat 64 (Sei.Float.f32ToF64 (c.sReg sm).toNat))) with pc := next }, bump m, true)
        -- VFP data-processing (CP10, single): VMOV-reg / VABS / VNEG
        else if (w >>> 24) &&& 0xf == 0b1110 && (w >>> 4) &&& 1 == 0 && (w >>> 8) &&& 0xf == 10 then
          let sd := (((w >>> 12) &&& 0xf) <<< 1) ||| ((w >>> 22) &&& 1)
          let sm := ((w &&& 0xf) <<< 1) ||| ((w >>> 5) &&& 1)
          let x := c.sReg sm
          if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xf == 0 && (w >>> 6) &&& 3 == 0b01 then  -- VMOV.F32 Sd,Sm
            ({ (c.setSReg sd x) with pc := next }, bump m, true)
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xf == 0 && (w >>> 6) &&& 3 == 0b11 then  -- VABS
            ({ (c.setSReg sd (x &&& 0x7fffffff)) with pc := next }, bump m, true)
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xf == 1 && (w >>> 6) &&& 3 == 0b01 then  -- VNEG
            ({ (c.setSReg sd (x ^^^ 0x80000000)) with pc := next }, bump m, true)
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xf == 1 && (w >>> 6) &&& 3 == 0b11 then  -- VSQRT
            ({ (c.setSReg sd (BitVec.ofNat 32 (Sei.Float.f32Sqrt x.toNat))) with pc := next }, bump m, true)
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xe == 0b0100 && (w >>> 6) &&& 1 == 1 then  -- VCMP/VCMPE
            let b := if (w >>> 16) &&& 1 == 1 then (0 : Word) else c.sReg sm    -- opc2 0101 ⇒ vs #0.0
            let nzcv := fcmp32 (c.sReg sd) b
            ({ c with fpscr := (c.fpscr &&& 0x0fffffff) ||| BitVec.ofNat 32 (nzcv <<< 28), pc := next }, bump m, true)
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 4) &&& 0xf == 0 then       -- VMOV.F32 Sd,#imm
            let imm8 := (((w >>> 16) &&& 0xf) <<< 4) ||| (w &&& 0xf)
            ({ (c.setSReg sd (BitVec.ofNat 32 (Sei.Float.expandImm Sei.Float.Fmt.f32 imm8))) with pc := next }, bump m, true)
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xe == 0b0010 && (w >>> 6) &&& 1 == 1 then  -- VCVTB/VCVTT (F16↔F32)
            let top := (w >>> 7) &&& 1 == 1               -- T: top vs bottom 16 bits
            if (w >>> 16) &&& 1 == 1 then                 -- F16.F32: single → half
              let h := Sei.Float.f32ToF16 (c.sReg sm).toNat
              let old := (c.sReg sd).toNat
              let merged := if top then (h <<< 16) ||| (old &&& 0xffff) else (old &&& 0xffff0000) ||| h
              ({ (c.setSReg sd (BitVec.ofNat 32 merged)) with pc := next }, bump m, true)
            else                                          -- F32.F16: half → single
              let src := (c.sReg sm).toNat
              let h := if top then (src >>> 16) &&& 0xffff else src &&& 0xffff
              ({ (c.setSReg sd (BitVec.ofNat 32 (Sei.Float.f16ToF32 h))) with pc := next }, bump m, true)
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xa == 0xa && (w >>> 6) &&& 1 == 1
                  && (((w &&& 0xf) <<< 1) ||| ((w >>> 5) &&& 1)) < (if (w >>> 7) &&& 1 == 1 then 32 else 16) then  -- VCVT fixed-point (F32 ↔ fixed)
            let signed := (w >>> 16) &&& 1 == 0
            let sx := if (w >>> 7) &&& 1 == 1 then 32 else 16
            let fbits := sx - (((w &&& 0xf) <<< 1) ||| ((w >>> 5) &&& 1))
            if (w >>> 18) &&& 1 == 1 then                  -- float → fixed
              ({ (c.setSReg sd (BitVec.ofNat 32 (Sei.Float.fToFixed Sei.Float.Fmt.f32 signed sx fbits 32 (c.sReg sd).toNat))) with pc := next }, bump m, true)
            else                                           -- fixed → float
              ({ (c.setSReg sd (BitVec.ofNat 32 (Sei.Float.fixedToF Sei.Float.Fmt.f32 signed sx fbits (c.sReg sd).toNat))) with pc := next }, bump m, true)
          -- arithmetic + multiply-accumulate + fused multiply-add (single).
          else if (w >>> 20) &&& 0xb == 0b0011 || (w >>> 20) &&& 0xb == 0b0010
               || (w >>> 20) &&& 0xb == 0b0001 || (w >>> 20) &&& 0xb == 0b0000
               || (w >>> 20) &&& 0xb == 0b1000 || (w >>> 20) &&& 0xb == 0b1010
               || (w >>> 20) &&& 0xb == 0b1001 then
            let sn := (((w >>> 16) &&& 0xf) <<< 1) ||| ((w >>> 7) &&& 1)
            let n := (c.sReg sn).toNat; let mm := x.toNat; let dv := (c.sReg sd).toNat
            let prod := Sei.Float.f32Mul n mm
            let neg (y : Nat) : Nat := y ^^^ 0x80000000
            let fma := Sei.Float.fma Sei.Float.Fmt.f32
            let op6 := (w >>> 6) &&& 1
            let r : Word := BitVec.ofNat 32 <|
              match (w >>> 20) &&& 0xb with
              | 0b1000 => Sei.Float.f32Div n mm                                  -- VDIV
              | 0b1010 => if op6 == 1 then fma (neg n) mm dv else fma n mm dv     -- VFMS / VFMA
              | 0b1001 => if op6 == 1 then fma (neg n) mm (neg dv) else fma n mm (neg dv)  -- VFNMA / VFNMS
              | 0b0011 => if op6 == 1 then Sei.Float.f32Sub n mm else Sei.Float.f32Add n mm  -- VSUB/VADD
              | 0b0010 => if op6 == 1 then neg prod else prod                    -- VNMUL / VMUL
              | 0b0001 => if op6 == 1 then Sei.Float.f32Add (neg dv) (neg prod)  -- VNMLA
                          else Sei.Float.f32Add (neg dv) prod                    -- VNMLS
              | _ => if op6 == 1 then Sei.Float.f32Add dv (neg prod)             -- VMLS
                     else Sei.Float.f32Add dv prod                               -- VMLA
            ({ (c.setSReg sd r) with pc := next }, bump m, true)
          else
            let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
            (c, bump m, true)
        -- VFP data-processing (CP11, double): VMOV/VABS/VNEG/VSQRT/VCMP + arithmetic
        else if (w >>> 24) &&& 0xf == 0b1110 && (w >>> 4) &&& 1 == 0 && (w >>> 8) &&& 0xf == 11 then
          let dd := (((w >>> 22) &&& 1) <<< 4) ||| ((w >>> 12) &&& 0xf)
          let dn := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let dm := (((w >>> 5) &&& 1) <<< 4) ||| (w &&& 0xf)
          let xn := (c.dReg dn).toNat; let xm := (c.dReg dm).toNat
          let put (v : Nat) : Cpu × Machine × Bool := ({ (c.setDReg dd (BitVec.ofNat 64 v)) with pc := next }, bump m, true)
          if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xf == 0 && (w >>> 6) &&& 3 == 0b01 then put xm  -- VMOV.F64
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xf == 0 && (w >>> 6) &&& 3 == 0b11 then put (xm &&& 0x7fffffffffffffff)  -- VABS
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xf == 1 && (w >>> 6) &&& 3 == 0b01 then put (xm ^^^ 0x8000000000000000)  -- VNEG
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xf == 1 && (w >>> 6) &&& 3 == 0b11 then put (Sei.Float.f64Sqrt xm)  -- VSQRT
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xe == 0b0100 && (w >>> 6) &&& 1 == 1 then  -- VCMP/VCMPE
            let b := if (w >>> 16) &&& 1 == 1 then 0 else xm
            let nzcv := Sei.Float.cmp Sei.Float.Fmt.f64 (c.dReg dd).toNat b
            ({ c with fpscr := (c.fpscr &&& 0x0fffffff) ||| BitVec.ofNat 32 (nzcv <<< 28), pc := next }, bump m, true)
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 4) &&& 0xf == 0 then       -- VMOV.F64 Dd,#imm
            let imm8 := (((w >>> 16) &&& 0xf) <<< 4) ||| (w &&& 0xf)
            put (Sei.Float.expandImm Sei.Float.Fmt.f64 imm8)
          else if (w >>> 20) &&& 0xb == 0xb && (w >>> 16) &&& 0xa == 0xa && (w >>> 6) &&& 1 == 1
                  && (((w &&& 0xf) <<< 1) ||| ((w >>> 5) &&& 1)) < (if (w >>> 7) &&& 1 == 1 then 32 else 16) then  -- VCVT fixed-point (F64 ↔ fixed)
            let signed := (w >>> 16) &&& 1 == 0
            let sx := if (w >>> 7) &&& 1 == 1 then 32 else 16
            let fbits := sx - (((w &&& 0xf) <<< 1) ||| ((w >>> 5) &&& 1))
            put (if (w >>> 18) &&& 1 == 1 then Sei.Float.fToFixed Sei.Float.Fmt.f64 signed sx fbits 64 (c.dReg dd).toNat
                 else Sei.Float.fixedToF Sei.Float.Fmt.f64 signed sx fbits (c.dReg dd).toNat)
          else if (w >>> 20) &&& 0xb == 0b0011 || (w >>> 20) &&& 0xb == 0b0010
               || (w >>> 20) &&& 0xb == 0b0001 || (w >>> 20) &&& 0xb == 0b0000
               || (w >>> 20) &&& 0xb == 0b1000 || (w >>> 20) &&& 0xb == 0b1010
               || (w >>> 20) &&& 0xb == 0b1001 then
            let dv := (c.dReg dd).toNat; let prod := Sei.Float.f64Mul xn xm
            let neg (y : Nat) : Nat := y ^^^ 0x8000000000000000
            let fma := Sei.Float.fma Sei.Float.Fmt.f64
            let op6 := (w >>> 6) &&& 1
            put (match (w >>> 20) &&& 0xb with
              | 0b1000 => Sei.Float.f64Div xn xm
              | 0b1010 => if op6 == 1 then fma (neg xn) xm dv else fma xn xm dv
              | 0b1001 => if op6 == 1 then fma (neg xn) xm (neg dv) else fma xn xm (neg dv)
              | 0b0011 => if op6 == 1 then Sei.Float.f64Sub xn xm else Sei.Float.f64Add xn xm
              | 0b0010 => if op6 == 1 then neg prod else prod
              | 0b0001 => if op6 == 1 then Sei.Float.f64Add (neg dv) (neg prod) else Sei.Float.f64Add (neg dv) prod
              | _ => if op6 == 1 then Sei.Float.f64Add dv (neg prod) else Sei.Float.f64Add dv prod)
          else
            let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
            (c, bump m, true)
        -- VMOV.32 Dd[idx],Rt / Rt,Dd[idx] — 32-bit D-register lane ↔ core register
        -- (the .8/.16 lane sizes are Advanced-SIMD byte/halfword access: deferred)
        else if (w >>> 24) &&& 0xf == 0b1110 && (w >>> 23) &&& 1 == 0 && (w >>> 4) &&& 1 == 1
                && (w >>> 8) &&& 0xf == 11 && (w >>> 22) &&& 1 == 0 && (w >>> 5) &&& 3 == 0 then
          let rt := (w >>> 12) &&& 0xf
          let dd := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let idx := (w >>> 21) &&& 1                       -- .32 lane: 0 (low) or 1 (high)
          let d := (c.dReg dd).toNat
          if (w >>> 20) &&& 1 == 1 then                     -- from SIMD: Rt = Dd[idx]
            let lane : Word := BitVec.ofNat 32 (if idx == 1 then d / 4294967296 else d % 4294967296)
            ({ (c.setR rt lane) with pc := next }, bump (m.emit (.reg rt lane)), true)
          else                                              -- to SIMD: Dd[idx] = Rt
            let rv := (c.rRead rt).toNat
            let nd := if idx == 1 then (d % 4294967296) ||| (rv <<< 32) else (d / 4294967296) <<< 32 ||| rv
            ({ (c.setDReg dd (BitVec.ofNat 64 nd)) with pc := next }, bump m, true)
        -- VDUP Dd/Qd, Rt — replicate a core register across all SIMD lanes.
        -- size from b:e (bit22:bit5); Q = bit21.
        else if (w >>> 24) &&& 0xf == 0b1110 && (w >>> 23) &&& 1 == 1 && (w >>> 8) &&& 0xf == 11
                && (w >>> 4) &&& 1 == 1 && (w >>> 20) &&& 1 == 0 && (w >>> 6) &&& 1 == 0 then
          let rt := (w >>> 12) &&& 0xf
          let esize := if (w >>> 22) &&& 1 == 1 then 8 else if (w >>> 5) &&& 1 == 1 then 16 else 32
          let q := (w >>> 21) &&& 1 == 1
          let dd := (((w >>> 7) &&& 1) <<< 4) ||| ((w >>> 16) &&& 0xf)
          let bits := if q then 128 else 64
          let r := Sei.Simd.rep esize (bits / esize) (c.rRead rt).toNat
          let c := if q then c.setQReg (dd / 2) r else c.setDReg dd (BitVec.ofNat 64 r)
          ({ c with pc := next }, bump m, true)
        -- VMOV core↔single + VMRS/VMSR (CP10, MCR/MRC form)
        else if (w >>> 24) &&& 0xf == 0b1110 && (w >>> 4) &&& 1 == 1 && (w >>> 8) &&& 0xf == 10 then
          let rt := (w >>> 12) &&& 0xf
          if (w >>> 21) &&& 0x7 == 0 && (w >>> 4) &&& 0x7 == 1 then               -- VMOV Sn,Rt / Rt,Sn
            let sn := (((w >>> 16) &&& 0xf) <<< 1) ||| ((w >>> 7) &&& 1)
            if (w >>> 20) &&& 1 == 0 then ({ (c.setSReg sn (c.rRead rt)) with pc := next }, bump m, true)  -- to FP
            else ({ (c.setR rt (c.sReg sn)) with pc := next }, bump (m.emit (.reg rt (c.sReg sn))), true)  -- from FP
          else if (w >>> 16) &&& 0xf == 0 then      -- FPSID: read-only CPU-model ID register
            -- value is the model's FPSID (here the Unicorn/Cortex-A default); VMSR is ignored
            if (w >>> 20) &&& 1 == 1 then
              let v : Word := BitVec.ofNat 32 0x410430f0
              ({ (c.setR rt v) with pc := next }, bump (m.emit (.reg rt v)), true)   -- VMRS Rt,FPSID
            else ({ c with pc := next }, bump m, true)                              -- VMSR FPSID,Rt (read-only)
          else if (w >>> 16) &&& 0xf == 8 then      -- FPEXC (VFP enable register)
            if (w >>> 20) &&& 1 == 1 then ({ (c.setR rt c.fpexc) with pc := next }, bump (m.emit (.reg rt c.fpexc)), true)
            else ({ c with fpexc := c.rRead rt, pc := next }, bump m, true)
          else if (w >>> 16) &&& 0xf != 1 then     -- VMRS/VMSR of other sysreg (MVFR0/1/2/…): NOP
            ({ c with pc := next }, bump m, true)
          else if (w >>> 20) &&& 1 == 1 then        -- VMRS Rt, FPSCR (Rt=15 ⇒ APSR_nzcv)
            if rt == 15 then
              ({ c with n := bit c.fpscr 31, z := bit c.fpscr 30, c := bit c.fpscr 29, v := bit c.fpscr 28, pc := next }, bump m, true)
            else ({ (c.setR rt c.fpscr) with pc := next }, bump (m.emit (.reg rt c.fpscr)), true)
          else ({ c with fpscr := c.rRead rt, pc := next }, bump m, true)         -- VMSR FPSCR, Rt
        -- Coprocessor MCR/MRC (CP15 system control; CP10/11 = VFP handled above,
        -- so exclude them here — double-precision VFP then falls through to undef)
        else if (w >>> 24) &&& 0xf == 0b1110 && (w >>> 4) &&& 1 == 1 && (w >>> 8) &&& 0xf == 15 then
          let isRead := (w >>> 20) &&& 1
          let opc1 := (w >>> 21) &&& 7
          let crn := (w >>> 16) &&& 0xf
          let rt := (w >>> 12) &&& 0xf
          let opc2 := (w >>> 5) &&& 7
          let crm := w &&& 0xf
          let key := (crn, opc1, crm, opc2)
          if isRead == 1 then
            let v := cp15Get c key
            let c := c.setR rt v
            ({ c with pc := next }, bump (m.emit (.cp15 "read" crn opc1 crm opc2 rt v)), true)
          else
            let v := c.rRead rt
            let c := cp15Set c key v
            ({ c with pc := next }, bump (m.emit (.cp15 "write" crn opc1 crm opc2 rt v)), true)
        -- MCR/MRC to other coprocessors (not CP15 / CP10 / CP11 VFP): MCR writes NOP;
        -- MRC reads mark not-decoded (we can't reproduce coprocessor register values).
        else if (w >>> 24) &&& 0xf == 0b1110 && (w >>> 4) &&& 1 == 1 then
          if (w >>> 20) &&& 1 == 1 then    -- MRC read: emit .unsupported so decoded=false
            let m := m.emit (.unsupported pc w (mnem w))
            ({ c with pc := next }, bump m, true)
          else ({ c with pc := next }, bump m, true)   -- MCR write: NOP
        -- SVC
        else if (w >>> 24) &&& 0xf == 0b1111 then
          let (c, m) := takeException c m "swi" next
          (c, bump m, true)
        -- LDR/STR word & unsigned byte (A5.3): imm or shifted-register offset,
        -- pre/post index, optional writeback.
        else if (w >>> 26) &&& 0x3 == 0b01 then
          let isReg := (w >>> 25) &&& 1
          if isReg == 1 && (w >>> 4) &&& 1 == 1 then            -- media instructions (A5.4)
            let rd := (w >>> 12) &&& 0xf
            let rm := w &&& 0xf
            let rn := (w >>> 16) &&& 0xf
            -- byte/halfword extends (Rn=1111, no add): SXTB/UXTB/SXTH/UXTH
            if (w >>> 20) &&& 0xfa == 0x6a && (w >>> 4) &&& 0xf == 0b0111 && rn == 0xf then
              let rot := ((w >>> 10) &&& 3) * 8
              let rotated := (c.rRead rm).rotateRight rot
              let half := (w >>> 22) &&& 1 == 1   -- bit22=1 ⇒ ...XTH, else ...XTB? (0x6b/0x6f are H)
              let signed := (w >>> 20) &&& 1 == 0 -- bit20=0 ⇒ signed (SXT), 1 ⇒ unsigned (UXT)
              let v : Word :=
                if (w >>> 20) &&& 0xf == 0xb || (w >>> 20) &&& 0xf == 0xf then   -- halfword (SXTH/UXTH)
                  if (w >>> 22) &&& 1 == 0 then (BitVec.ofNat 16 rotated.toNat).signExtend 32 else rotated &&& 0xffff
                else                                                            -- byte (SXTB/UXTB)
                  if (w >>> 22) &&& 1 == 0 then (BitVec.ofNat 8 rotated.toNat).signExtend 32 else rotated &&& 0xff
              ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- REV / REV16
            else if (w >>> 20) &&& 0xff == 0x6b && (w >>> 8) &&& 0xf == 0xf
                    && ((w >>> 4) &&& 0xf == 0b0011 || (w >>> 4) &&& 0xf == 0b1011) then
              let x := c.rRead rm
              let v : Word := if (w >>> 4) &&& 0xf == 0b0011 then        -- REV: reverse 4 bytes
                  ((x &&& 0xff) <<< 24) ||| (((x >>> 8) &&& 0xff) <<< 16) |||
                  (((x >>> 16) &&& 0xff) <<< 8) ||| ((x >>> 24) &&& 0xff)
                else                                                     -- REV16: swap bytes in each halfword
                  (((x >>> 8) &&& 0xff)) ||| ((x &&& 0xff) <<< 8) |||
                  (((x >>> 24) &&& 0xff) <<< 16) ||| (((x >>> 16) &&& 0xff) <<< 24)
              ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- UBFX / SBFX (bitfield extract)
            else if (w >>> 23) &&& 0x3 == 0b11 && (w >>> 4) &&& 0x7 == 0b101 then
              let widthm1 := (w >>> 16) &&& 0x1f
              let lsb := (w >>> 7) &&& 0x1f
              let src := c.rRead rm                                     -- Rn is bits[3:0] here
              let field := (src >>> lsb) &&& (BitVec.ofNat 32 ((1 <<< (widthm1 + 1)) - 1))
              let v : Word := if (w >>> 22) &&& 1 == 1 then field        -- UBFX (unsigned)
                else (BitVec.ofNat (widthm1 + 1) field.toNat).signExtend 32  -- SBFX (signed)
              ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- BFI / BFC (bitfield insert/clear)
            else if (w >>> 21) &&& 0x7f == 0b0111110 && (w >>> 4) &&& 0x7 == 0b001 then
              let msb := (w >>> 16) &&& 0x1f
              let lsb := (w >>> 7) &&& 0x1f
              let maskN := if msb < lsb then 0 else (((1 <<< (msb - lsb + 1)) - 1) <<< lsb)
              let mask := BitVec.ofNat 32 maskN
              let ins := if rm == 0xf then (0 : Word)                   -- Rn=1111 ⇒ BFC (clear)
                         else ((c.rRead rm) <<< lsb) &&& mask           -- BFI (insert from Rn)
              let v := ((c.rRead rd) &&& (~~~ mask)) ||| ins
              ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- RBIT / REVSH
            else if (w >>> 20) &&& 0xff == 0x6f && (w >>> 8) &&& 0xf == 0xf
                    && ((w >>> 4) &&& 0xf == 3 || (w >>> 4) &&& 0xf == 0xb) then
              let src := c.rRead rm
              let v : Word :=
                if (w >>> 4) &&& 0xf == 3 then
                  (List.range 32).foldl (fun (acc : Word) (i : Nat) =>
                    acc ||| (if (src >>> i) &&& 1 == 1 then (1 : Word) <<< (31 - i) else (0 : Word))) (0 : Word)
                else
                  let lo := (src &&& 0xff) <<< 8 ||| ((src >>> 8) &&& 0xff)
                  (BitVec.ofNat 16 lo.toNat).signExtend 32
              ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- SXTAB / SXTAH / UXTAB / UXTAH (Rn ≠ 1111)
            else if (w >>> 20) &&& 0xfa == 0x6a && (w >>> 4) &&& 0xf == 7 && rn != 0xf then
              let rot := ((w >>> 10) &&& 3) * 8
              let rotated := (c.rRead rm).rotateRight rot
              let ext : Word :=
                if (w >>> 20) &&& 0xf == 0xb || (w >>> 20) &&& 0xf == 0xf then
                  if (w >>> 22) &&& 1 == 0 then (BitVec.ofNat 16 rotated.toNat).signExtend 32
                  else rotated &&& 0xffff
                else
                  if (w >>> 22) &&& 1 == 0 then (BitVec.ofNat 8 rotated.toNat).signExtend 32
                  else rotated &&& 0xff
              let v := c.rRead rn + ext
              ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- SXTB16 / UXTB16 / SXTAB16 / UXTAB16
            else if (w >>> 20) &&& 0xfb == 0x68 && (w >>> 4) &&& 0xf == 7 then
              let rot := ((w >>> 10) &&& 3) * 8
              let rotated := (c.rRead rm).rotateRight rot
              let signed16 := (w >>> 22) &&& 1 == 0
              let extBot : Word :=
                if signed16 then (BitVec.ofNat 8 rotated.toNat).signExtend 32 &&& 0xffff
                else rotated &&& 0xff
              let extTop : Word :=
                if signed16 then (BitVec.ofNat 8 ((rotated >>> 16).toNat)).signExtend 32 &&& 0xffff
                else (rotated >>> 16) &&& 0xff
              let addBot : Word := if rn != 0xf then c.rRead rn &&& 0xffff else 0
              let addTop : Word := if rn != 0xf then (c.rRead rn) >>> 16 else 0
              let lo := (extBot + addBot) &&& 0xffff
              let hi := (extTop + addTop) &&& 0xffff
              let v : Word := (hi <<< 16) ||| lo
              ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- PKHBT / PKHTB
            else if (w >>> 20) &&& 0xff == 0x68 && ((w >>> 4) &&& 0xf == 1 || (w >>> 4) &&& 0xf == 5) then
              let imm5 := (w >>> 7) &&& 0x1f
              let tbform := (w >>> 6) &&& 1 == 1
              let v : Word :=
                if tbform then
                  let shN : Nat := if imm5 == 0 then 32 else imm5
                  let shifted := BitVec.ofInt 32 ((c.rRead rm).toInt >>> shN)
                  (c.rRead rn &&& 0xffff0000) ||| (shifted &&& 0xffff)
                else
                  let shifted : Word := c.rRead rm <<< imm5
                  (shifted &&& 0xffff0000) ||| (c.rRead rn &&& 0xffff)
              ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- SEL (GE=0 at init → all bytes from Rm)
            else if (w >>> 20) &&& 0xff == 0x68 && (w >>> 4) &&& 0xf == 0xb && (w >>> 8) &&& 0xf == 0xf then
              let v := c.rRead rm
              ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- SSAT / USAT / SSAT16 / USAT16
            else if ((w >>> 20) &&& 0xff == 0x6a || (w >>> 20) &&& 0xff == 0x6e)
                    && ((w >>> 4) &&& 0xf == 1 || (w >>> 4) &&& 0xf == 5 || (w >>> 4) &&& 0xf == 3) then
              let isSigned := (w >>> 22) &&& 1 == 0
              let satImm := (w >>> 16) &&& 0xf
              if (w >>> 4) &&& 0xf == 3 then
                let sat := satImm + 1
                let clamp := fun (x : Int) =>
                  if isSigned then max (-Int.ofNat (1 <<< (sat-1))) (min (Int.ofNat (1 <<< (sat-1)) - 1) x)
                  else max (0 : Int) (min (Int.ofNat (1 <<< (sat-1)) - 1) x)
                let hi16 : Int := ((c.rRead rm >>> 16) &&& 0xffff).toNat
                let lo16 : Int := (c.rRead rm &&& 0xffff).toNat
                let rHi := BitVec.ofInt 32 (clamp hi16) &&& 0xffff
                let rLo := BitVec.ofInt 32 (clamp lo16) &&& 0xffff
                let v : Word := (rHi <<< 16) ||| rLo
                ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
              else
                let sat := satImm + 1
                let isAsr := (w >>> 4) &&& 0xf == 5
                let imm5 := (w >>> 7) &&& 0x1f
                let shN : Nat := if isAsr && imm5 == 0 then 32 else imm5
                let src : Int := if isAsr then (c.rRead rm).toInt >>> shN
                                 else ((c.rRead rm) <<< imm5).toInt
                let maxV : Int := Int.ofNat (1 <<< (sat - 1)) - 1
                let minV : Int := if isSigned then -Int.ofNat (1 <<< (sat - 1)) else 0
                let v : Word := BitVec.ofInt 32 (max minV (min maxV src))
                ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- Parallel arithmetic (SADD/SSUB/QADD/QSUB/SHADD/SHSUB/UADD/USUB/UQADD/UQSUB/UHADD/UHSUB)
            else if (w >>> 24) &&& 0xf == 6 && (w >>> 23) &&& 1 == 0
                    && (w >>> 8) &&& 0xf == 0xf && rn != 0xf then
              let opFam := (w >>> 20) &&& 0x7
              let opType := (w >>> 4) &&& 0xf
              let rnW := c.rRead rn; let rmW := c.rRead rm
              let rnH := rnW >>> 16; let rnL := rnW &&& 0xffff
              let rmH := rmW >>> 16; let rmL := rmW &&& 0xffff
              let s16 := fun (x : Word) => (BitVec.ofNat 16 x.toNat).signExtend 32 |>.toInt
              let u16 := fun (x : Word) => (x.toNat : Int)
              let lh := fun (x : Word) => if opFam < 4 then s16 x else u16 x
              let s8 := fun (x : Word) => (BitVec.ofNat 8 x.toNat).signExtend 32 |>.toInt
              let u8 := fun (x : Word) => (x.toNat : Int)
              let lb := fun (x : Word) => if opFam < 4 then s8 x else u8 x
              let op16 := fun (a b : Int) (isAdd : Bool) =>
                let raw := if isAdd then a + b else a - b
                let r : Int :=
                  if opFam == 1 || opFam == 5 then ((raw % 65536) + 65536) % 65536
                  else if opFam == 2 then max (-32768 : Int) (min 32767 raw)
                  else if opFam == 6 then max (0 : Int) (min 65535 raw)
                  else if opFam == 3 then raw >>> 1
                  else (if raw < 0 then raw + 131072 else raw) >>> 1
                BitVec.ofInt 32 r &&& 0xffff
              let op8 := fun (a b : Int) (isAdd : Bool) =>
                let raw := if isAdd then a + b else a - b
                let r : Int :=
                  if opFam == 1 || opFam == 5 then ((raw % 256) + 256) % 256
                  else if opFam == 2 then max (-128 : Int) (min 127 raw)
                  else if opFam == 6 then max (0 : Int) (min 255 raw)
                  else if opFam == 3 then raw >>> 1
                  else (if raw < 0 then raw + 512 else raw) >>> 1
                BitVec.ofInt 32 r &&& 0xff
              let v : Word :=
                if opType == 9 || opType == 15 then
                  let isAdd := opType == 9
                  let b0n := rnL &&& 0xff; let b1n := (rnL >>> 8) &&& 0xff
                  let b2n := rnH &&& 0xff; let b3n := (rnH >>> 8) &&& 0xff
                  let b0m := rmL &&& 0xff; let b1m := (rmL >>> 8) &&& 0xff
                  let b2m := rmH &&& 0xff; let b3m := (rmH >>> 8) &&& 0xff
                  (op8 (lb b0n) (lb b0m) isAdd) |||
                  ((op8 (lb b1n) (lb b1m) isAdd) <<< 8) |||
                  ((op8 (lb b2n) (lb b2m) isAdd) <<< 16) |||
                  ((op8 (lb b3n) (lb b3m) isAdd) <<< 24)
                else
                  let (resH, resL) :=
                    if opType == 1 then (op16 (lh rnH) (lh rmH) true,  op16 (lh rnL) (lh rmL) true)
                    else if opType == 3 then (op16 (lh rnH) (lh rmL) true, op16 (lh rnL) (lh rmH) false)
                    else if opType == 5 then (op16 (lh rnH) (lh rmL) false, op16 (lh rnL) (lh rmH) true)
                    else (op16 (lh rnH) (lh rmH) false, op16 (lh rnL) (lh rmL) false)
                  (resH <<< 16) ||| resL
              ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
            -- SDIV / UDIV
            else if (w >>> 20) &&& 0xfd == 0x71 && (w >>> 4) &&& 0xf == 1 then
              let rs := (w >>> 8) &&& 0xf
              let isSig := (w >>> 21) &&& 1 == 0
              let v : Word :=
                if isSig then
                  let q := if (c.rRead rs).toInt == 0 then 0
                            else (c.rRead rm).toInt / (c.rRead rs).toInt
                  BitVec.ofInt 32 q
                else
                  let q := if (c.rRead rs).toNat == 0 then 0
                            else (c.rRead rm).toNat / (c.rRead rs).toNat
                  BitVec.ofNat 32 q
              let rdDst2 := (w >>> 16) &&& 0xf
              ({ (c.setR rdDst2 v) with pc := next }, bump (m.emit (.reg rdDst2 v)), true)
            -- SMLAD / SMLADX / SMLSD / SMLSDX / SMUAD / SMUADX / SMUSD / SMUSDX
            else if (w >>> 20) &&& 0xff == 0x70 && (w >>> 4) &&& 1 == 1 && (w >>> 7) &&& 1 == 0 then
              let rs := (w >>> 8) &&& 0xf
              let ra := (w >>> 12) &&& 0xf
              let rmV := c.rRead rm; let rsV := c.rRead rs
              let isSubOp := (w >>> 6) &&& 1 == 1
              let isExchange := (w >>> 5) &&& 1 == 1
              let rmBot : Int := (BitVec.ofNat 16 rmV.toNat).signExtend 32 |>.toInt
              let rmTop : Int := (BitVec.ofNat 16 (rmV.toNat >>> 16)).signExtend 32 |>.toInt
              let rsBot : Int := (BitVec.ofNat 16 rsV.toNat).signExtend 32 |>.toInt
              let rsTop : Int := (BitVec.ofNat 16 (rsV.toNat >>> 16)).signExtend 32 |>.toInt
              let (rsA, rsB) := if isExchange then (rsTop, rsBot) else (rsBot, rsTop)
              let prod := if isSubOp then rmBot * rsA - rmTop * rsB
                          else rmBot * rsA + rmTop * rsB
              let rdDst := (w >>> 16) &&& 0xf
              let raVal : Int := if ra == 0xf then 0 else (c.rRead ra).toInt
              let result := BitVec.ofInt 32 (prod + raVal)
              ({ (c.setR rdDst result) with pc := next }, bump (m.emit (.reg rdDst result)), true)
            -- SMLALD / SMLALDX / SMLSLD / SMLSLDX
            else if (w >>> 20) &&& 0xff == 0x74 && (w >>> 4) &&& 1 == 1 then
              let rdHi := (w >>> 16) &&& 0xf
              let rdLo := (w >>> 12) &&& 0xf
              let rs := (w >>> 8) &&& 0xf
              let isSubOp := (w >>> 6) &&& 1 == 1
              let isExchange := (w >>> 5) &&& 1 == 1
              let rmV := c.rRead rm; let rsV := c.rRead rs
              let rmBot : Int := (BitVec.ofNat 16 rmV.toNat).signExtend 32 |>.toInt
              let rmTop : Int := (BitVec.ofNat 16 (rmV.toNat >>> 16)).signExtend 32 |>.toInt
              let rsBot : Int := (BitVec.ofNat 16 rsV.toNat).signExtend 32 |>.toInt
              let rsTop : Int := (BitVec.ofNat 16 (rsV.toNat >>> 16)).signExtend 32 |>.toInt
              let (rsA, rsB) := if isExchange then (rsTop, rsBot) else (rsBot, rsTop)
              let prod := if isSubOp then rmBot * rsA - rmTop * rsB
                          else rmBot * rsA + rmTop * rsB
              let accHi : Int := (c.rRead rdHi).toInt
              let accLo : Int := (c.rRead rdLo).toNat
              let acc64 := accHi * 4294967296 + accLo
              let full64 := BitVec.ofInt 64 (prod + acc64)
              let lo : Word := BitVec.ofNat 32 (full64.toNat % 4294967296)
              let hi : Word := BitVec.ofNat 32 (full64.toNat / 4294967296)
              let c := (c.setR rdLo lo).setR rdHi hi
              ({ c with pc := next }, bump ((m.emit (.reg rdLo lo)).emit (.reg rdHi hi)), true)
            -- SMMLA / SMMLAR / SMMLS / SMMLSR / SMMUL / SMMULR
            else if (w >>> 20) &&& 0xff == 0x75 && (w >>> 4) &&& 1 == 1 then
              let rs := (w >>> 8) &&& 0xf
              let ra := (w >>> 12) &&& 0xf
              let isRounding := (w >>> 5) &&& 1 == 1
              let isSub := (w >>> 6) &&& 1 == 1
              let rmI := (c.rRead rm).toInt; let rsI := (c.rRead rs).toInt
              let prod : Int := rmI * rsI
              let raShifted : Int := if ra == 0xf then 0 else (c.rRead ra).toInt * 4294967296
              let sum64 := if isSub then raShifted - prod else raShifted + prod
              let rounded := sum64 + if isRounding then 2147483648 else 0
              let rdDst3 := (w >>> 16) &&& 0xf
              let result : Word := BitVec.ofInt 32 (rounded >>> 32)
              ({ (c.setR rdDst3 result) with pc := next }, bump (m.emit (.reg rdDst3 result)), true)
            -- USAD8 / USADA8
            else if (w >>> 20) &&& 0xff == 0x78 && (w >>> 4) &&& 0xf == 1 then
              let rdDst4 := (w >>> 16) &&& 0xf
              let rs := (w >>> 8) &&& 0xf
              let ra := (w >>> 12) &&& 0xf
              let rmV := c.rRead rm; let rsV := c.rRead rs
              let absDiff := fun (a b : Nat) => if a ≥ b then a - b else b - a
              let sad := absDiff (rmV &&& 0xff).toNat (rsV &&& 0xff).toNat
                       + absDiff ((rmV >>> 8) &&& 0xff).toNat ((rsV >>> 8) &&& 0xff).toNat
                       + absDiff ((rmV >>> 16) &&& 0xff).toNat ((rsV >>> 16) &&& 0xff).toNat
                       + absDiff ((rmV >>> 24) &&& 0xff).toNat ((rsV >>> 24) &&& 0xff).toNat
              let acc := if ra == 0xf then 0 else (c.rRead ra).toNat
              let v : Word := BitVec.ofNat 32 (sad + acc)
              ({ (c.setR rdDst4 v) with pc := next }, bump (m.emit (.reg rdDst4 v)), true)
            else
              let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
              (c, bump m, true)
          -- Rn=PC is valid only as the immediate-offset, no-writeback literal form;
          -- any register-offset / indexed / writeback PC base is UNPREDICTABLE → defer.
          else if (w >>> 16) &&& 0xf == 0xf
                  && ((w >>> 25) &&& 1 == 1 || (w >>> 24) &&& 1 == 0 || (w >>> 21) &&& 1 == 1) then
            let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
            (c, bump m, true)
          else
            let p := (w >>> 24) &&& 1
            let u := (w >>> 23) &&& 1
            let b := (w >>> 22) &&& 1
            let wbit := (w >>> 21) &&& 1
            let load := (w >>> 20) &&& 1
            let rn := (w >>> 16) &&& 0xf
            let rt := (w >>> 12) &&& 0xf
            let offset : Word := if isReg == 1
              then (immShift (c.rRead (w &&& 0xf)) ((w >>> 5) &&& 3) ((w >>> 7) &&& 0x1f) c.c).1
              else BitVec.ofNat 32 (w &&& 0xfff)
            let base := c.rRead rn
            let off := if u == 1 then base + offset else base - offset
            let addr := if p == 1 then off else base           -- pre-indexed uses offset; post uses base
            let writeBack := p == 0 || wbit == 1
            let width := if b == 1 then 8 else 32
            let storeVal := c.rRead rt                          -- capture before writeback
            let cWb := if writeBack then c.setR rn off else c
            if load == 1 then
              match c.memRead m addr width with
              | (.ok v, m) =>
                let c := cWb.setR rt v                          -- rt wins if rt == rn
                if rt == 15 then ({ c with pc := v &&& ~~~ (1 : Word), tbit := v &&& 1 == 1 }, bump m, true)
                else ({ c with pc := next }, bump m, true)
              | (.error _, m) =>
                let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" (pc + 8); (c, bump m, true)
            else
              match c.memWrite m addr storeVal width with
              | (.ok _, m) => ({ cWb with pc := next }, bump m, true)
              | (.error _, m) =>
                let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" (pc + 8); (c, bump m, true)
        -- Multiply family (bits[27:24]=0000, bits[7:4]=1001): MUL/MLA + long.
        else if (w >>> 26) &&& 0x3 == 0b00 && (w >>> 25) &&& 1 == 0
                && (w >>> 24) &&& 0xf == 0 && (w >>> 4) &&& 0xf == 0b1001 then
          let s := (w >>> 20) &&& 1
          let rdHi := (w >>> 16) &&& 0xf      -- Rd (MUL/MLA) or RdHi (long)
          let rdLo := (w >>> 12) &&& 0xf      -- Ra (MLA) or RdLo (long)
          let rs := (w >>> 8) &&& 0xf
          let rm := w &&& 0xf
          let a := c.rRead rm; let b := c.rRead rs
          match (w >>> 21) &&& 0xf with
          | 0 =>                              -- MUL
            let r := a * b
            let c := c.setR rdHi r
            ({ (if s == 1 then setNZ c r else c) with pc := next }, bump (m.emit (.reg rdHi r)), true)
          | 1 =>                              -- MLA
            let r := a * b + c.rRead rdLo
            let c := c.setR rdHi r
            ({ (if s == 1 then setNZ c r else c) with pc := next }, bump (m.emit (.reg rdHi r)), true)
          | 2 =>                              -- UMAAL: {rdHi,rdLo} = Rm*Rs + rdHi + rdLo
            let p := a.toNat * b.toNat + (c.rRead rdHi).toNat + (c.rRead rdLo).toNat
            let lo : Word := BitVec.ofNat 32 (p % 4294967296)
            let hi : Word := BitVec.ofNat 32 (p / 4294967296)
            ({ ((c.setR rdLo lo).setR rdHi hi) with pc := next }, bump (m.emit (.reg rdHi hi)), true)
          | 3 =>                              -- MLS: Rd = Ra - Rm*Rs
            let r := c.rRead rdLo - a * b
            let c := c.setR rdHi r
            ({ c with pc := next }, bump (m.emit (.reg rdHi r)), true)
          | mop =>                            -- UMULL(4)/UMLAL(5)/SMULL(6)/SMLAL(7)
            if mop < 4 then
              let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
              (c, bump m, true)
            else
              let signed := mop == 6 || mop == 7
              let accum := mop == 5 || mop == 7
              let prodN : Nat := if signed then (BitVec.ofInt 64 (a.toInt * b.toInt)).toNat
                                 else a.toNat * b.toNat
              let accN : Nat := if accum then (c.rRead rdHi).toNat * 4294967296 + (c.rRead rdLo).toNat else 0
              let full := (prodN + accN) % 18446744073709551616
              let lo : Word := BitVec.ofNat 32 (full % 4294967296)
              let hi : Word := BitVec.ofNat 32 (full / 4294967296)
              let c := (c.setR rdLo lo).setR rdHi hi
              let c := if s == 1 then { c with n := bit hi 31, z := full == 0 } else c
              ({ c with pc := next }, bump (m.emit (.reg rdHi hi)), true)
        -- Synchronization: LDREX/STREX/LDREXD/STREXD/LDREXB/STREXB/LDREXH/STREXH
        -- bits[7:4]=1001, bits[27:20] in 0x18..0x1F. STREX always "fails" (Rd←1, no store)
        -- to match the Unicorn oracle (no exclusive monitor modelled).
        else if (w >>> 26) &&& 0x3 == 0 && (w >>> 25) &&& 1 == 0 && (w >>> 4) &&& 0xf == 0b1001
                && (w >>> 20) &&& 0xf8 == 0x18 then
          let op20 := (w >>> 20) &&& 0xff
          let rn := (w >>> 16) &&& 0xf
          let rt := (w >>> 12) &&& 0xf
          let base := c.rRead rn
          let dabt (c : Cpu) (m : Machine) := let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" (pc + 8); (c, bump m, true)
          if op20 == 0x19 then                        -- LDREX: Rt ← [Rn]
            match c.memRead m base 32 with
            | (.ok v, m) => ({ (c.setR rt v) with pc := next }, bump m, true)
            | (.error _, m) => dabt c m
          else if op20 == 0x1b then                   -- LDREXD: Rt ← [Rn], Rt+1 ← [Rn+4]
            let (r0, m) := c.memRead m base 32
            let (r1, m) := c.memRead m (base + 4) 32
            match r0, r1 with
            | .ok v0, .ok v1 =>
              ({ ((c.setR rt v0).setR (rt + 1) v1) with pc := next }, bump m, true)
            | _, _ => dabt c m
          else if op20 == 0x1d then                   -- LDREXB: Rt ← ZeroExtend([Rn][7:0])
            match c.memRead m base 8 with
            | (.ok v, m) => ({ (c.setR rt (v &&& 0xff)) with pc := next }, bump m, true)
            | (.error _, m) => dabt c m
          else if op20 == 0x1f then                   -- LDREXH: Rt ← ZeroExtend([Rn][15:0])
            match c.memRead m base 16 with
            | (.ok v, m) => ({ (c.setR rt (v &&& 0xffff)) with pc := next }, bump m, true)
            | (.error _, m) => dabt c m
          else                                        -- STREX/STREXD/STREXB/STREXH: always fail (Rd←1)
            let rd := rt                              -- for STREX: Rd = bits[15:12]
            let c := c.setR rd (BitVec.ofNat 32 1)
            ({ c with pc := next }, bump (m.emit (.reg rd (BitVec.ofNat 32 1))), true)
        -- SWP/SWPB and remaining sync space: fall through to undef
        else if (w >>> 26) &&& 0x3 == 0 && (w >>> 25) &&& 1 == 0 && (w >>> 4) &&& 0xf == 0b1001 then
          let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
          (c, bump m, true)
        -- Extra load/store (A5.2.8): halfword, signed byte/halfword, and dual.
        else if (w >>> 26) &&& 0x3 == 0b00 && (w >>> 25) &&& 1 == 0
                && (w >>> 4) &&& 1 == 1 && (w >>> 7) &&& 1 == 1 && (w >>> 5) &&& 3 != 0 then
          -- Rn=PC with register-offset / post-index / writeback is UNPREDICTABLE → defer.
          if (w >>> 16) &&& 0xf == 0xf
             && ((w >>> 22) &&& 1 == 0 || (w >>> 24) &&& 1 == 0 || (w >>> 21) &&& 1 == 1) then
            let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
            (c, bump m, true)
          else
          let op2 := (w >>> 5) &&& 3            -- 01=H, 10=SB|LDRD, 11=SH|STRD
          let p := (w >>> 24) &&& 1
          let u := (w >>> 23) &&& 1
          let imm := (w >>> 22) &&& 1
          let wbit := (w >>> 21) &&& 1
          let load := (w >>> 20) &&& 1
          let rn := (w >>> 16) &&& 0xf
          let rt := (w >>> 12) &&& 0xf
          let offset : Word := if imm == 1 then BitVec.ofNat 32 ((((w >>> 8) &&& 0xf) <<< 4) ||| (w &&& 0xf))
                               else c.rRead (w &&& 0xf)
          let base := c.rRead rn
          let off := if u == 1 then base + offset else base - offset
          let addr := if p == 1 then off else base
          let cWb := if p == 0 || wbit == 1 then c.setR rn off else c
          let dabt (c : Cpu) (m : Machine) := let (c, m) := takeException c (m.emit (.note "data_abort")) "dabt" (pc + 8); (c, bump m, true)
          if load == 1 then                    -- LDRH / LDRSB / LDRSH
            let width := if op2 == 2 then 8 else 16
            match c.memRead m addr width with
            | (.ok v, m) =>
              let ext : Word := if op2 == 1 then v &&& 0xffff
                                else if op2 == 2 then (BitVec.ofNat 8 v.toNat).signExtend 32
                                else (BitVec.ofNat 16 v.toNat).signExtend 32
              ({ (cWb.setR rt ext) with pc := next }, bump m, true)
            | (.error _, m) => dabt c m
          else if op2 == 1 then                -- STRH
            match c.memWrite m addr (c.rRead rt &&& 0xffff) 16 with
            | (.ok _, m) => ({ cWb with pc := next }, bump m, true)
            | (.error _, m) => dabt c m
          else if op2 == 2 then                -- LDRD (Rt, Rt+1) ← [addr], [addr+4]
            let (r0, m) := c.memRead m addr 32
            let (r1, m) := c.memRead m (addr + 4) 32
            match r0, r1 with
            | .ok v0, .ok v1 =>
              -- Load first, then recompute writeback using post-load state (handles
              -- Rm==Rt+1 UNPREDICTABLE case the same way hardware does: new Rm used).
              let cL := (c.setR rt v0).setR (rt + 1) v1
              let offL : Word := if imm == 1 then off
                                 else let rm := w &&& 0xf
                                      if u == 1 then base + cL.rRead rm else base - cL.rRead rm
              let cWbL := if p == 0 || wbit == 1 then cL.setR rn offL else cL
              ({ cWbL with pc := next }, bump m, true)
            | _, _ => dabt c m
          else                                 -- STRD [addr], [addr+4] ← Rt, Rt+1
            let v0 := c.rRead rt; let v1 := c.rRead (rt + 1)
            match c.memWrite m addr v0 32 with
            | (.ok _, m) =>
              match c.memWrite m (addr + 4) v1 32 with
              | (.ok _, m) => ({ cWb with pc := next }, bump m, true)
              | (.error _, m) => dabt c m
            | (.error _, m) => dabt c m
        -- CLZ (count leading zeros)
        else if (w >>> 20) &&& 0xff == 0x16 && (w >>> 4) &&& 0xf == 1 then
          let rd := (w >>> 12) &&& 0xf
          let v := BitVec.ofNat 32 (clz32 (c.rRead (w &&& 0xf)))
          ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
        -- MRS: move CPSR/SPSR → Rd
        else if (w >>> 26) &&& 0x3 == 0 && (w >>> 23) &&& 0x1f == 0b00010 && (w >>> 20) &&& 3 == 0
                && (w >>> 25) &&& 1 == 0 && (w >>> 16) &&& 0xf == 0xf && (w >>> 4) &&& 0xf == 0 then
          let rd := (w >>> 12) &&& 0xf
          let v := if (w >>> 22) &&& 1 == 1 then spsrGet c c.mode else packCpsr c
          ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
        -- MSR: move register/immediate → CPSR fields (privileged), masked
        else if (w >>> 26) &&& 0x3 == 0 && (w >>> 23) &&& 0x1b == 0b00010 && (w >>> 20) &&& 3 == 2
                && (w >>> 22) &&& 1 == 0 && ((w >>> 25) &&& 1 == 1 || (w >>> 4) &&& 0xf == 0) then  -- MSR CPSR (reg form bits[7:4]=0, excludes DSP)
          let mask := (w >>> 16) &&& 0xf
          let value : Word := if (w >>> 25) &&& 1 == 1 then BitVec.ofNat 32 (rotImm w) else c.rRead (w &&& 0xf)
          let vN := value.toNat
          let c := if mask &&& 8 == 8 then            -- flags field (NZCV)
            { c with n := bit value 31, z := bit value 30, c := bit value 29, v := bit value 28 } else c
          let c := if mask &&& 1 == 1 then             -- control field (mode/I/F/T)
            let c := c.switchMode (vN &&& 0x1f)
            { c with iMask := (vN >>> 7) &&& 1 == 1, fMask := (vN >>> 6) &&& 1 == 1, tbit := (vN >>> 5) &&& 1 == 1 }
            else c
          ({ c with pc := next }, bump m, true)
        -- Miscellaneous / DSP space (bits[27:23]=00010, S=0): MRS/MSR/CLZ/BX handled above.
        else if (w >>> 25) &&& 0x7 == 0b000 && (w >>> 23) &&& 0x3 == 0b10 && (w >>> 20) &&& 1 == 0 then
          let op20 := (w >>> 20) &&& 0x1f
          -- BXJ: branch to Rm, no Jazelle (treat as BX)
          if (w >>> 4) &&& 0xffffff == 0x12fff2 then
            let target := c.rRead (w &&& 0xf)
            ({ c with pc := target &&& 0xfffffffe, tbit := (target &&& 1) == 1 }, bump m, true)
          -- BLX_r: branch with link to Rm
          else if (w >>> 4) &&& 0xffffff == 0x12fff3 then
            let target := c.rRead (w &&& 0xf)
            let lr := next
            let c := c.setR 14 lr
            ({ c with pc := target &&& 0xfffffffe, tbit := (target &&& 1) == 1 },
             bump (m.emit (.reg 14 lr)), true)
          -- ERET: exception return (PC ← LR)
          else if op20 == 0x16 && (w >>> 4) &&& 0xf == 6 then
            ({ c with pc := c.rRead 14 }, bump m, true)
          -- QADD/QSUB/QDADD/QDSUB: bits[7:4]=0101, bits[22:21] select op
          else if (w >>> 4) &&& 0xf == 5 then
            let qop := (w >>> 21) &&& 3
            let rd := (w >>> 12) &&& 0xf
            let aI := (c.rRead (w &&& 0xf)).toInt
            let bI := (c.rRead ((w >>> 16) &&& 0xf)).toInt
            let sat := fun (x : Int) => if x > 2147483647 then (2147483647 : Int) else if x < -2147483648 then (-2147483648 : Int) else x
            let result : Word := BitVec.ofInt 32 (sat (if qop == 0 then aI + bI
              else if qop == 1 then aI - bI
              else if qop == 2 then aI + sat (2 * bI)
              else aI - sat (2 * bI)))
            let c := c.setR rd result
            ({ c with pc := next }, bump (m.emit (.reg rd result)), true)
          -- SMLAxy: bits[24:20]=0x10, bit7=1, bit4=0 (16×16 signed multiply-accumulate)
          else if op20 == 0x10 && (w >>> 7) &&& 1 == 1 && (w >>> 4) &&& 1 == 0 then
            let rd := (w >>> 16) &&& 0xf
            let rmV := c.rRead (w &&& 0xf)
            let rsV := c.rRead ((w >>> 8) &&& 0xf)
            let xH : Int := (BitVec.ofNat 16 (if (w >>> 5) &&& 1 == 0 then rmV.toNat &&& 0xffff else rmV.toNat >>> 16)).signExtend 32 |>.toInt
            let yH : Int := (BitVec.ofNat 16 (if (w >>> 6) &&& 1 == 0 then rsV.toNat &&& 0xffff else rsV.toNat >>> 16)).signExtend 32 |>.toInt
            let result := BitVec.ofInt 32 (xH * yH + (c.rRead ((w >>> 12) &&& 0xf)).toInt)
            let c := c.setR rd result
            ({ c with pc := next }, bump (m.emit (.reg rd result)), true)
          -- SMLAWy/SMULWy: bits[24:20]=0x12, bit7=1, bit4=0 (32×16 signed multiply ± accumulate)
          else if op20 == 0x12 && (w >>> 7) &&& 1 == 1 && (w >>> 4) &&& 1 == 0 then
            let rd := (w >>> 16) &&& 0xf
            let rmI := (c.rRead (w &&& 0xf)).toInt
            let rsV := c.rRead ((w >>> 8) &&& 0xf)
            let rsH : Int := (BitVec.ofNat 16 (if (w >>> 6) &&& 1 == 0 then rsV.toNat &&& 0xffff else rsV.toNat >>> 16)).signExtend 32 |>.toInt
            let prod : Int := (rmI * rsH) / 65536
            let raI : Int := if (w >>> 5) &&& 1 == 0 then (c.rRead ((w >>> 12) &&& 0xf)).toInt else 0
            let result := BitVec.ofInt 32 (prod + raI)
            let c := c.setR rd result
            ({ c with pc := next }, bump (m.emit (.reg rd result)), true)
          -- SMLALxy: bits[24:20]=0x14, bit7=1, bit4=0 (16×16 signed multiply-accumulate long)
          else if op20 == 0x14 && (w >>> 7) &&& 1 == 1 && (w >>> 4) &&& 1 == 0 then
            let rdHi := (w >>> 16) &&& 0xf
            let rdLo := (w >>> 12) &&& 0xf
            let rmV := c.rRead (w &&& 0xf)
            let rsV := c.rRead ((w >>> 8) &&& 0xf)
            let xH : Int := (BitVec.ofNat 16 (if (w >>> 5) &&& 1 == 0 then rmV.toNat &&& 0xffff else rmV.toNat >>> 16)).signExtend 32 |>.toInt
            let yH : Int := (BitVec.ofNat 16 (if (w >>> 6) &&& 1 == 0 then rsV.toNat &&& 0xffff else rsV.toNat >>> 16)).signExtend 32 |>.toInt
            let prodN := (BitVec.ofInt 64 (xH * yH)).toNat
            let accN := (c.rRead rdHi).toNat * 4294967296 + (c.rRead rdLo).toNat
            let full := (prodN + accN) % 18446744073709551616
            let lo : Word := BitVec.ofNat 32 (full % 4294967296)
            let hi : Word := BitVec.ofNat 32 (full / 4294967296)
            let c := (c.setR rdLo lo).setR rdHi hi
            ({ c with pc := next }, bump (m.emit (.reg rdHi hi)), true)
          -- SMULxy: bits[24:20]=0x16, bit7=1 (16×16 signed multiply, no accumulate)
          else if op20 == 0x16 && (w >>> 7) &&& 1 == 1 then
            let rd := (w >>> 16) &&& 0xf
            let rmV := c.rRead (w &&& 0xf)
            let rsV := c.rRead ((w >>> 8) &&& 0xf)
            let xH : Int := (BitVec.ofNat 16 (if (w >>> 5) &&& 1 == 0 then rmV.toNat &&& 0xffff else rmV.toNat >>> 16)).signExtend 32 |>.toInt
            let yH : Int := (BitVec.ofNat 16 (if (w >>> 6) &&& 1 == 0 then rsV.toNat &&& 0xffff else rsV.toNat >>> 16)).signExtend 32 |>.toInt
            let result := BitVec.ofInt 32 (xH * yH)
            let c := c.setR rd result
            ({ c with pc := next }, bump (m.emit (.reg rd result)), true)
          else
            let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
            (c, bump m, true)
        -- Data processing (A5.2): full shifter operand + 16 opcodes.
        else if (w >>> 26) &&& 0x3 == 0b00 then
          let isImm := (w >>> 25) &&& 1
          let opcode := (w >>> 21) &&& 0xf
          let s := (w >>> 20) &&& 1
          let rn := (w >>> 16) &&& 0xf
          let rd := (w >>> 12) &&& 0xf
          -- MOVW / MOVT (immediate, opcode 0x8/0xA with bit25)
          if isImm == 1 && ((w >>> 20) &&& 0xff == 0x30 || (w >>> 20) &&& 0xff == 0x34) then
            let imm16 := ((w >>> 4) &&& 0xf000) ||| (w &&& 0xfff)
            let v := if (w >>> 22) &&& 1 == 0 then BitVec.ofNat 32 imm16
                     else ((c.rRead rd) &&& 0xffff) ||| (BitVec.ofNat 32 (imm16 <<< 16))
            ({ (c.setR rd v) with pc := next }, bump (m.emit (.reg rd v)), true)
          else
            -- shifter operand (value + carry-out)
            let (op2, shCarry) :=
              if isImm == 1 then
                let v := BitVec.ofNat 32 (rotImm w)
                (v, if (w >>> 8) &&& 0xf == 0 then c.c else bit v 31)
              else
                let rm := c.rRead (w &&& 0xf)
                let stype := (w >>> 5) &&& 3
                if (w >>> 4) &&& 1 == 1 then regShift rm stype (((c.rRead ((w >>> 8) &&& 0xf)).toNat) &&& 0xff) c.c
                else immShift rm stype ((w >>> 7) &&& 0x1f) c.c
            let a := c.rRead rn
            -- (result, carry-out, overflow); logical ops take the shifter carry.
            let (r, cOut, vOut) : Word × Bool × Bool :=
              match opcode with
              | 0x0 => (a &&& op2, shCarry, c.v)                                    -- AND
              | 0x1 => (a ^^^ op2, shCarry, c.v)                                    -- EOR
              | 0x2 => addWithCarry a (~~~ op2) true                               -- SUB
              | 0x3 => addWithCarry (~~~ a) op2 true                               -- RSB
              | 0x4 => addWithCarry a op2 false                                    -- ADD
              | 0x5 => addWithCarry a op2 c.c                                      -- ADC
              | 0x6 => addWithCarry a (~~~ op2) c.c                                -- SBC
              | 0x7 => addWithCarry (~~~ a) op2 c.c                                -- RSC
              | 0x8 => (a &&& op2, shCarry, c.v)                                    -- TST
              | 0x9 => (a ^^^ op2, shCarry, c.v)                                    -- TEQ
              | 0xA => addWithCarry a (~~~ op2) true                               -- CMP
              | 0xB => addWithCarry a op2 false                                    -- CMN
              | 0xC => (a ||| op2, shCarry, c.v)                                    -- ORR
              | 0xD => (op2, shCarry, c.v)                                          -- MOV
              | 0xE => (a &&& (~~~ op2), shCarry, c.v)                              -- BIC
              | _   => (~~~ op2, shCarry, c.v)                                      -- MVN
            let writes := opcode < 0x8 || opcode > 0xB    -- TST/TEQ/CMP/CMN are flags-only
            let setF (c : Cpu) : Cpu := { c with n := bit r 31, z := r == 0, c := cOut, v := vOut }
            if !writes then ({ setF c with pc := next }, bump m, true)   -- compares: S is implied
            else if rd == 15 then
              let c := c.setR 15 r
              if s == 1 then
                let spsr := spsrGet c c.mode
                let oldMode := c.mode
                let c := unpackCpsr c spsr
                ({ c with pc := r }, bump (m.emit (.exception "return" r oldMode)), true)
              else ({ c with pc := r }, bump m, true)
            else
              let c := c.setR rd r
              let c := if s == 1 then setF c else c
              ({ c with pc := next }, bump (m.emit (.reg rd r)), true)
        else
          let (c, m) := takeException c (m.emit (.unsupported pc w (mnem w))) "undef" next
          (c, bump m, true)

def runArm (fuel : Nat) (s : St) : St :=
  Sei.Core.run (fun (s : St) =>
    let (c, m) := s
    if c.halted then (s, false)
    else let (c', m', cont) := step c m; ((c', m'), cont)) fuel s

/-! ### Assembler (canonical A32 encodings) -/

def AL : Nat := 0xE

/-- imm8/rot encoding for a data-processing immediate (searches rotations). -/
def rotateImm (value : Nat) : Nat × Nat := Id.run do
  let v := value &&& 0xffffffff
  for rot in [0:16] do
    let amt := (rot * 2) % 32
    let rotated := if amt == 0 then v else ((v <<< amt) ||| (v >>> (32 - amt))) &&& 0xffffffff
    if rotated ≤ 0xff then return (rotated, rot)
  return (0, 0)

def bvw (n : Nat) : Word := BitVec.ofNat 32 n

def dpImm (opcode rd rn value : Nat) (cond : Nat := AL) (s : Nat := 0) : Word :=
  let (imm8, rot) := rotateImm value
  bvw ((cond <<< 28) ||| (1 <<< 25) ||| (opcode <<< 21) ||| (s <<< 20) |||
       (rn <<< 16) ||| (rd <<< 12) ||| (rot <<< 8) ||| imm8)

def MOV (rd value : Nat) (cond : Nat := AL) (s : Nat := 0) : Word := dpImm 0xD rd 0 value cond s
def SUB (rd rn value : Nat) (cond : Nat := AL) (s : Nat := 0) : Word := dpImm 0x2 rd rn value cond s
def BX (rm : Nat) (cond : Nat := AL) : Word := bvw ((cond <<< 28) ||| 0x12FFF10 ||| rm)

def MOVW (rd imm16 : Nat) (cond : Nat := AL) : Word :=
  bvw ((cond <<< 28) ||| (0x30 <<< 20) ||| ((imm16 >>> 12) <<< 16) ||| (rd <<< 12) ||| (imm16 &&& 0xfff))
def MOVT (rd imm16 : Nat) (cond : Nat := AL) : Word :=
  bvw ((cond <<< 28) ||| (0x34 <<< 20) ||| ((imm16 >>> 12) <<< 16) ||| (rd <<< 12) ||| (imm16 &&& 0xfff))
def LDR (rt rn imm12 : Nat) (cond : Nat := AL) : Word :=
  bvw ((cond <<< 28) ||| (0b01 <<< 26) ||| (1 <<< 24) ||| (1 <<< 23) ||| (1 <<< 20) |||
       (rn <<< 16) ||| (rt <<< 12) ||| (imm12 &&& 0xfff))
def STR (rt rn imm12 : Nat) (cond : Nat := AL) : Word :=
  bvw ((cond <<< 28) ||| (0b01 <<< 26) ||| (1 <<< 24) ||| (1 <<< 23) |||
       (rn <<< 16) ||| (rt <<< 12) ||| (imm12 &&& 0xfff))
/-- Branch to absolute `target` from instruction at `cur`. Uses BitVec
    subtraction so backward branches encode a correct (two's-complement) offset. -/
def B (target cur : Nat) (cond : Nat := AL) : Word :=
  let diff : Word := BitVec.ofNat 32 target - BitVec.ofNat 32 (cur + 8)
  let off := (diff >>> 2).toNat &&& 0xffffff
  bvw ((cond <<< 28) ||| (0b101 <<< 25) ||| off)
def MCR (rt crn crm : Nat) (opc1 opc2 cp : Nat := 0) (cond : Nat := AL) : Word :=
  bvw ((cond <<< 28) ||| (0b1110 <<< 24) ||| (opc1 <<< 21) ||| (crn <<< 16) ||| (rt <<< 12) |||
       ((if cp == 0 then 15 else cp) <<< 8) ||| (opc2 <<< 5) ||| (1 <<< 4) ||| crm)
def MRC (rt crn crm : Nat) (opc1 opc2 cp : Nat := 0) (cond : Nat := AL) : Word :=
  bvw ((cond <<< 28) ||| (0b1110 <<< 24) ||| (opc1 <<< 21) ||| (1 <<< 20) ||| (crn <<< 16) |||
       (rt <<< 12) ||| ((if cp == 0 then 15 else cp) <<< 8) ||| (opc2 <<< 5) ||| (1 <<< 4) ||| crm)
def SUBS_pc_lr (imm : Nat) (cond : Nat := AL) : Word := dpImm 0x2 15 14 imm cond 1
def MOVS_pc_lr (cond : Nat := AL) : Word :=
  bvw ((cond <<< 28) ||| (0xD <<< 21) ||| (1 <<< 20) ||| (15 <<< 12) ||| 14)
def WORDV (v : Nat) : Word := bvw v

def assemble (words : List Word) (little : Bool) : List Byte :=
  words.flatMap (fun w => encodeBytes little w.toNat 4)

end Sei.Isa.Arm
