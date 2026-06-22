/-
MIPS32r2 (little-endian) slice over the SEI Lean core — pure, total, typed effects.
Covers E05: GPRs with branch-delay slots, a CP0 subset (Status/Cause/EPC/Count/
Compare/BadVAddr), Count==Compare timer interrupt, the general exception vector
0x80000180, ERET, SYSCALL, and kseg0/kseg1 + a simple TLB.

Unicorn-validated (tools/mipsgen/) for: ALU-R (ADDU/SUBU/AND/OR/XOR/NOR/SLL/SRL/SRA/
SLLV/SRLV/SRAV/SLT/SLTU), ALU-I (ADDIU/ANDI/ORI/XORI/SLTI/SLTIU/LUI), HI/LO
(MULT/MULTU/DIV/DIVU/MFHI/MFLO/MTHI/MTLO), SPECIAL2 (MUL/CLZ/CLO), SPECIAL3 (EXT/INS).
-/
import Sei.Core
import Sei.Float
open Sei.Core

namespace Sei.Isa.Mips

-- CP0 (rd, sel)
def INDEX : Nat × Nat := (0, 0)
def ENTRYLO : Nat × Nat := (2, 0)
def ENTRYHI : Nat × Nat := (10, 0)
def BADVADDR : Nat × Nat := (8, 0)
def COUNT : Nat × Nat := (9, 0)
def COMPARE : Nat × Nat := (11, 0)
def STATUS : Nat × Nat := (12, 0)
def CAUSE : Nat × Nat := (13, 0)
def EPC : Nat × Nat := (14, 0)

def EXC_VECTOR : Word := 0x80000180
def EXC_INT : Nat := 0
def EXC_TLBL : Nat := 2
def EXC_TLBS : Nat := 3
def EXC_SYS : Nat := 8
def EXC_BP  : Nat := 9
def EXC_OVF : Nat := 12
def EXC_TR  : Nat := 13

structure Cpu where
  regs : Array Word := (List.replicate 32 (0 : Word)).toArray
  pc : Word := 0x80000000
  npc : Word := 0x80000004
  hi : Word := 0
  lo : Word := 0
  llbit : Bool := false
  cp0 : List ((Nat × Nat) × Word) := []
  tlb : List (Nat × Nat) := []          -- vpn → pfn (4 KB pages)
  halted : Bool := false
  fprs : Array Word := (List.replicate 32 (0 : Word)).toArray
  fcr31 : Word := 0
  deriving Inhabited

abbrev St := Cpu × Machine

def Cpu.r (c : Cpu) (i : Nat) : Word := c.regs.getD i 0
def Cpu.setR (c : Cpu) (i : Nat) (v : Word) : Cpu :=
  if i == 0 then c else { c with regs := c.regs.setIfInBounds i v }
def Cpu.c0 (c : Cpu) (k : Nat × Nat) : Word := (c.cp0.find? (·.1 == k)).map (·.2) |>.getD 0
def Cpu.setC0 (c : Cpu) (k : Nat × Nat) (v : Word) : Cpu :=
  { c with cp0 := (k, v) :: c.cp0.filter (·.1 != k) }
def Cpu.addTlb (c : Cpu) (vpn pfn : Nat) : Cpu :=
  { c with tlb := (vpn / 0x1000 * 0x1000, pfn / 0x1000 * 0x1000) :: c.tlb }

/-- kseg0/kseg1 map directly; useg requires a TLB entry. -/
def Cpu.translate (c : Cpu) (v : Word) : Option Word :=
  let n := v.toNat
  if 0x80000000 ≤ n ∧ n < 0xC0000000 then some (BitVec.ofNat 32 (n &&& 0x1FFFFFFF))
  else
    let vpn := n / 0x1000 * 0x1000
    match c.tlb.find? (·.1 == vpn) with
    | some (_, pfn) => some (BitVec.ofNat 32 (pfn ||| (n &&& 0xFFF)))
    | none => none

def bit (n : Nat) : Word := BitVec.ofNat 32 (1 <<< n)

/-- Enter the general exception vector with EPC/EXL/Cause set. If the faulting
    instruction is in a branch delay slot (`npc ≠ pc+4`), EPC points to the
    *branch* and `Cause.BD` (bit 31) is set, so ERET re-runs the branch (N4). -/
def enterException (c : Cpu) (m : Machine) (exccode : Nat) (badv : Option Word) : Cpu × Machine :=
  let c : Cpu := { c with llbit := false }
  let inDelay := c.npc != c.pc + 4
  let epc := if inDelay then c.pc - 4 else c.pc
  let c := c.setC0 EPC epc
  let codeCause := (c.c0 CAUSE &&& ~~~ (BitVec.ofNat 32 (0x1f <<< 2))) ||| BitVec.ofNat 32 (exccode <<< 2)
  let cause := if inDelay then codeCause ||| bit 31 else codeCause &&& ~~~ (bit 31)
  let c := c.setC0 CAUSE cause
  let c := c.setC0 STATUS (c.c0 STATUS ||| 2)         -- EXL
  let c := match badv with | some b => c.setC0 BADVADDR b | none => c
  let m := m.emit (.exception "mips" EXC_VECTOR exccode)
  ({ c with pc := EXC_VECTOR, npc := EXC_VECTOR + 4 }, m)

/-- Advance Count (always — the increment is part of the state), raise IP7 on a
    Compare match, and take an Int if enabled. -/
def timerAndIrq (c : Cpu) (m : Machine) : Cpu × Machine × Bool :=
  let c := c.setC0 COUNT (c.c0 COUNT + 1)
  let (c, m) :=
    if c.c0 COMPARE != 0 && c.c0 COUNT == c.c0 COMPARE then
      (c.setC0 CAUSE (c.c0 CAUSE ||| bit 15), m.emit (.timer "compare_match" (c.c0 COUNT)))
    else (c, m)
  let st := (c.c0 STATUS).toNat
  let cause := (c.c0 CAUSE).toNat
  let pending := (cause >>> 8) &&& (st >>> 8) &&& 0xff
  if (st &&& 1 == 1) && (st &&& 2 == 0) && pending != 0 then
    let (c, m) := enterException c (m.emit (.irqLine "timer" true)) EXC_INT none
    (c, m, true)
  else (c, m, false)

inductive Ctl where
  | normal (branch : Option Word)
  | normalLikely (branch : Option Word)   -- annul delay slot if not taken
  | exception | halt | eret
  deriving Inhabited

-- Signed interpretation of a 32-bit word.
private def w2i (v : Word) : Int :=
  let n := v.toNat
  if n ≥ 0x80000000 then Int.ofNat n - Int.ofNat 0x100000000 else Int.ofNat n

-- Wrap a signed integer to a 32-bit word (two's complement).
private def i2w (i : Int) : Word :=
  BitVec.ofNat 32 (if i < 0 then (i + Int.ofNat 0x100000000).toNat else i.toNat)

-- Truncated integer division toward zero (MIPS DIV semantics, like C).
-- Lean 4's default `Int./` is floor division; this gives T-division explicitly.
private def tdiv (a b : Int) : Int :=
  if (a < 0) == (b < 0)
  then Int.ofNat (a.natAbs / b.natAbs)
  else -(Int.ofNat (a.natAbs / b.natAbs))

private def tmod (a b : Int) : Int := a - b * tdiv a b

-- Arithmetic right shift of a 32-bit value by sa bits (floor = fill with sign).
private def sar32 (v : Nat) (sa : Nat) : Nat :=
  let msb := v >>> 31
  let shifted := v >>> sa
  if msb == 1 && sa > 0
  then shifted ||| ((0xFFFFFFFF <<< (32 - sa)) &&& 0xFFFFFFFF)
  else shifted

-- Count leading zeros in a 32-bit value.
private def clz32 (n : Nat) : Nat :=
  (List.range 32).takeWhile (fun i => n &&& (1 <<< (31 - i)) == 0) |>.length

-- Count leading ones in a 32-bit value.
private def clo32 (n : Nat) : Nat :=
  (List.range 32).takeWhile (fun i => n &&& (1 <<< (31 - i)) != 0) |>.length

-- FPR helpers
private def Cpu.fr (c : Cpu) (i : Nat) : Word := c.fprs.getD i 0

private def Cpu.frD (c : Cpu) (i : Nat) : Nat :=
  ((c.fr (i + 1)).toNat <<< 32) ||| (c.fr i).toNat

private def Cpu.setFrD (c : Cpu) (i : Nat) (v : Nat) : Cpu :=
  { c with fprs := (c.fprs.setIfInBounds i (BitVec.ofNat 32 (v &&& 0xFFFFFFFF))).setIfInBounds (i + 1) (BitVec.ofNat 32 ((v >>> 32) &&& 0xFFFFFFFF)) }

private def writeFpr (c : Cpu) (i : Nat) (isD : Bool) (v : Nat) : Cpu :=
  if isD then c.setFrD i v
  else { c with fprs := c.fprs.setIfInBounds i (BitVec.ofNat 32 (v &&& 0xFFFFFFFF)) }

-- FCR31 condition-code bit: cc=0 → bit 23, cc>0 → bit 24+cc
private def fccPos (cc : Nat) : Nat := if cc == 0 then 23 else 24 + cc

-- CEIL.W: round toward +∞ via truncate-then-compare
private def ceilW (f : Sei.Float.Fmt) (x : Nat) : Nat :=
  let t := Sei.Float.fToInt f true false x
  if t == 0x7FFFFFFF then t
  else
    let tf := Sei.Float.i32ToF f (t &&& 0xFFFFFFFF)
    let nzcv := Sei.Float.cmp f tf x
    if nzcv &&& 8 != 0 then (t + 1) &&& 0xFFFFFFFF else t

-- FLOOR.W: round toward -∞ via truncate-then-compare
private def floorW (f : Sei.Float.Fmt) (x : Nat) : Nat :=
  let t := Sei.Float.fToInt f true false x
  if t == 0x80000000 then t
  else
    let tf := Sei.Float.i32ToF f (t &&& 0xFFFFFFFF)
    let nzcv := Sei.Float.cmp f tf x
    if nzcv == 2 then (t + 0xFFFFFFFF) &&& 0xFFFFFFFF else t

private def emitReg (c : Cpu) (m : Machine) (i : Nat) (v : Word) : Cpu × Machine :=
  (c.setR i v, m.emit (.reg i v))

def execute (c : Cpu) (m : Machine) (pc : Word) (op rs rt rd sa funct imm : Nat) (simm : Word)
    : Cpu × Machine × Ctl :=
  match op with
  | 0x00 =>  -- SPECIAL
    match funct with
    | 0x00 => let (c, m) := emitReg c m rd (c.r rt <<< sa); (c, m, .normal none)       -- SLL/NOP
    | 0x01 =>                                                                             -- MOVCI
      let cc := (rt >>> 2) &&& 7; let tf := rt &&& 1
      let fccVal := (c.fcr31.toNat >>> fccPos cc) &&& 1
      let cond := if tf == 0 then fccVal == 0 else fccVal == 1
      if cond then let (c, m) := emitReg c m rd (c.r rs); (c, m, .normal none)
      else (c, m, .normal none)
    | 0x02 =>                                                                             -- SRL/ROTR
      let v := (c.r rt).toNat
      let result : Nat := if rs != 0 then  -- rs=1 → ROTR
        let sh := sa % 32
        if sh == 0 then v else (v >>> sh) ||| ((v <<< (32 - sh)) &&& 0xFFFFFFFF)
      else v >>> sa  -- SRL
      let (c, m) := emitReg c m rd (BitVec.ofNat 32 result)
      (c, m, .normal none)
    | 0x03 =>                                                                             -- SRA
      let (c, m) := emitReg c m rd (BitVec.ofNat 32 (sar32 (c.r rt).toNat sa))
      (c, m, .normal none)
    | 0x04 =>                                                                             -- SLLV
      let shamt := (c.r rs).toNat &&& 31
      let (c, m) := emitReg c m rd (c.r rt <<< shamt)
      (c, m, .normal none)
    | 0x06 =>                                                                             -- SRLV/ROTRV
      let shamt := (c.r rs).toNat &&& 31
      let v := (c.r rt).toNat
      let result : Nat := if sa &&& 1 != 0 then  -- sa bit0=1 → ROTRV
        if shamt == 0 then v else (v >>> shamt) ||| ((v <<< (32 - shamt)) &&& 0xFFFFFFFF)
      else v >>> shamt  -- SRLV
      let (c, m) := emitReg c m rd (BitVec.ofNat 32 result)
      (c, m, .normal none)
    | 0x07 =>                                                                             -- SRAV
      let shamt := (c.r rs).toNat &&& 31
      let (c, m) := emitReg c m rd (BitVec.ofNat 32 (sar32 (c.r rt).toNat shamt))
      (c, m, .normal none)
    | 0x08 => (c, m, .normal (some (c.r rs)))                                            -- JR
    | 0x09 =>                                                                             -- JALR
      let (c, m) := emitReg c m rd (pc + 8)
      (c, m, .normal (some (c.r rs)))
    | 0x0A =>                                                                             -- MOVZ
      if (c.r rt).toNat == 0 then let (c, m) := emitReg c m rd (c.r rs); (c, m, .normal none)
      else (c, m, .normal none)
    | 0x0B =>                                                                             -- MOVN
      if (c.r rt).toNat != 0 then let (c, m) := emitReg c m rd (c.r rs); (c, m, .normal none)
      else (c, m, .normal none)
    | 0x0C => let (c, m) := enterException c m EXC_SYS none; (c, m, .exception)        -- SYSCALL
    | 0x0D => let (c, m) := enterException c m EXC_BP  none; (c, m, .exception)        -- BREAK
    | 0x0F => (c, m, .normal none)                                                       -- SYNC: NOP
    | 0x10 =>                                                                             -- MFHI
      let (c, m) := emitReg c m rd c.hi
      (c, m, .normal none)
    | 0x11 => ({ c with hi := c.r rs }, m, .normal none)                                -- MTHI
    | 0x12 =>                                                                             -- MFLO
      let (c, m) := emitReg c m rd c.lo
      (c, m, .normal none)
    | 0x13 => ({ c with lo := c.r rs }, m, .normal none)                                -- MTLO
    | 0x18 =>                                                                             -- MULT
      let a := w2i (c.r rs); let b := w2i (c.r rt)
      let prod := a * b
      let prod64 : Int := if prod < 0 then prod + Int.ofNat (1 <<< 64) else prod
      let n := prod64.toNat
      ({ c with lo := BitVec.ofNat 32 (n &&& 0xFFFFFFFF),
                hi := BitVec.ofNat 32 ((n >>> 32) &&& 0xFFFFFFFF) }, m, .normal none)
    | 0x19 =>                                                                             -- MULTU
      let prod := (c.r rs).toNat * (c.r rt).toNat
      ({ c with lo := BitVec.ofNat 32 (prod &&& 0xFFFFFFFF),
                hi := BitVec.ofNat 32 ((prod >>> 32) &&& 0xFFFFFFFF) }, m, .normal none)
    | 0x1A =>                                                                             -- DIV
      let a := w2i (c.r rs); let b := w2i (c.r rt)
      if b == 0 then (c, m, .normal none)
      else ({ c with lo := i2w (tdiv a b), hi := i2w (tmod a b) }, m, .normal none)
    | 0x1B =>                                                                             -- DIVU
      let a := (c.r rs).toNat; let b := (c.r rt).toNat
      if b == 0 then (c, m, .normal none)
      else ({ c with lo := BitVec.ofNat 32 (a / b), hi := BitVec.ofNat 32 (a % b) }, m, .normal none)
    | 0x20 =>                                                                             -- ADD (OV trap)
      let a := c.r rs; let b := c.r rt; let sum := a + b
      if a.toNat >>> 31 == b.toNat >>> 31 && a.toNat >>> 31 != sum.toNat >>> 31 then
        let (c, m) := enterException c m EXC_OVF none; (c, m, .exception)
      else let (c, m) := emitReg c m rd sum; (c, m, .normal none)
    | 0x21 => let (c, m) := emitReg c m rd (c.r rs + c.r rt); (c, m, .normal none)     -- ADDU
    | 0x22 =>                                                                             -- SUB (OV trap)
      let a := c.r rs; let b := c.r rt; let diff := a - b
      if a.toNat >>> 31 != b.toNat >>> 31 && a.toNat >>> 31 != diff.toNat >>> 31 then
        let (c, m) := enterException c m EXC_OVF none; (c, m, .exception)
      else let (c, m) := emitReg c m rd diff; (c, m, .normal none)
    | 0x23 => let (c, m) := emitReg c m rd (c.r rs - c.r rt); (c, m, .normal none)     -- SUBU
    | 0x24 => let (c, m) := emitReg c m rd (c.r rs &&& c.r rt); (c, m, .normal none)   -- AND
    | 0x25 => let (c, m) := emitReg c m rd (c.r rs ||| c.r rt); (c, m, .normal none)   -- OR
    | 0x26 => let (c, m) := emitReg c m rd (c.r rs ^^^ c.r rt); (c, m, .normal none)   -- XOR
    | 0x27 => let (c, m) := emitReg c m rd (~~~ (c.r rs ||| c.r rt)); (c, m, .normal none) -- NOR
    | 0x2A =>                                                                             -- SLT
      let v : Word := if w2i (c.r rs) < w2i (c.r rt) then 1 else 0
      let (c, m) := emitReg c m rd v; (c, m, .normal none)
    | 0x2B =>                                                                             -- SLTU
      let v : Word := if (c.r rs).toNat < (c.r rt).toNat then 1 else 0
      let (c, m) := emitReg c m rd v; (c, m, .normal none)
    | 0x30 =>                                                                             -- TGE
      if w2i (c.r rs) >= w2i (c.r rt) then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x31 =>                                                                             -- TGEU
      if (c.r rs).toNat >= (c.r rt).toNat then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x32 =>                                                                             -- TLT
      if w2i (c.r rs) < w2i (c.r rt) then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x33 =>                                                                             -- TLTU
      if (c.r rs).toNat < (c.r rt).toNat then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x34 =>                                                                             -- TEQ
      if c.r rs == c.r rt then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x36 =>                                                                             -- TNE
      if c.r rs != c.r rt then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | _ => ({ c with halted := true }, m.emit (.note "reserved_special"), .halt)
  | 0x01 =>  -- REGIMM
    match rt with
    | 0x00 =>  -- BLTZ
      (c, m, .normal (if w2i (c.r rs) < 0 then some (pc + 4 + simm * 4) else none))
    | 0x01 =>  -- BGEZ
      (c, m, .normal (if w2i (c.r rs) ≥ 0 then some (pc + 4 + simm * 4) else none))
    | 0x08 =>  -- TGEI
      if w2i (c.r rs) >= w2i simm then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x09 =>  -- TGEIU
      if (c.r rs).toNat >= simm.toNat then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x0A =>  -- TLTI
      if w2i (c.r rs) < w2i simm then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x0B =>  -- TLTIU
      if (c.r rs).toNat < simm.toNat then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x0C =>  -- TEQI
      if c.r rs == simm then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x0E =>  -- TNEI
      if c.r rs != simm then let (c, m) := enterException c m EXC_TR none; (c, m, .exception)
      else (c, m, .normal none)
    | 0x02 =>  -- BLTZL (branch-likely)
      (c, m, .normalLikely (if w2i (c.r rs) < 0 then some (pc + 4 + simm * 4) else none))
    | 0x03 =>  -- BGEZL (branch-likely)
      (c, m, .normalLikely (if w2i (c.r rs) ≥ 0 then some (pc + 4 + simm * 4) else none))
    | 0x10 =>  -- BLTZAL
      let (c, m) := emitReg c m 31 (pc + 8)
      (c, m, .normal (if w2i (c.r rs) < 0 then some (pc + 4 + simm * 4) else none))
    | 0x11 =>  -- BGEZAL
      let (c, m) := emitReg c m 31 (pc + 8)
      (c, m, .normal (if w2i (c.r rs) ≥ 0 then some (pc + 4 + simm * 4) else none))
    | 0x12 =>  -- BLTZALL (branch-and-link-likely: always link, like BLTZAL)
      let (c, m) := emitReg c m 31 (pc + 8)
      (c, m, .normalLikely (if w2i (c.r rs) < 0 then some (pc + 4 + simm * 4) else none))
    | 0x13 =>  -- BGEZALL (branch-and-link-likely: always link, like BGEZAL)
      let (c, m) := emitReg c m 31 (pc + 8)
      (c, m, .normalLikely (if w2i (c.r rs) ≥ 0 then some (pc + 4 + simm * 4) else none))
    | 0x1F => (c, m, .normal none)  -- SYNCI: sync instruction cache (NOP in simulation)
    | _ => ({ c with halted := true }, m.emit (.note "reserved_regimm"), .halt)
  | 0x02 =>  -- J
    let index := ((rs <<< 21) ||| (rt <<< 16) ||| imm) &&& 0x3FFFFFF
    (c, m, .normal (some (((pc + 4) &&& 0xF0000000) ||| BitVec.ofNat 32 (index <<< 2))))
  | 0x03 =>  -- JAL
    let index := ((rs <<< 21) ||| (rt <<< 16) ||| imm) &&& 0x3FFFFFF
    let target := ((pc + 4) &&& 0xF0000000) ||| BitVec.ofNat 32 (index <<< 2)
    let (c, m) := emitReg c m 31 (pc + 8)
    (c, m, .normal (some target))
  | 0x04 =>  -- BEQ
    (c, m, .normal (if c.r rs == c.r rt then some (pc + 4 + simm * 4) else none))
  | 0x05 =>  -- BNE
    (c, m, .normal (if c.r rs != c.r rt then some (pc + 4 + simm * 4) else none))
  | 0x14 =>  -- BEQL (branch-likely)
    (c, m, .normalLikely (if c.r rs == c.r rt then some (pc + 4 + simm * 4) else none))
  | 0x15 =>  -- BNEL (branch-likely)
    (c, m, .normalLikely (if c.r rs != c.r rt then some (pc + 4 + simm * 4) else none))
  | 0x16 =>  -- BLEZL (branch-likely)
    (c, m, .normalLikely (if w2i (c.r rs) ≤ 0 then some (pc + 4 + simm * 4) else none))
  | 0x17 =>  -- BGTZL (branch-likely)
    (c, m, .normalLikely (if w2i (c.r rs) > 0 then some (pc + 4 + simm * 4) else none))
  | 0x06 =>  -- BLEZ
    (c, m, .normal (if w2i (c.r rs) ≤ 0 then some (pc + 4 + simm * 4) else none))
  | 0x07 =>  -- BGTZ
    (c, m, .normal (if w2i (c.r rs) > 0 then some (pc + 4 + simm * 4) else none))
  | 0x08 =>  -- ADDI (OV trap)
    let a := c.r rs; let b := simm; let sum := a + b
    if a.toNat >>> 31 == b.toNat >>> 31 && a.toNat >>> 31 != sum.toNat >>> 31 then
      let (c, m) := enterException c m EXC_OVF none; (c, m, .exception)
    else let (c, m) := emitReg c m rt sum; (c, m, .normal none)
  | 0x09 => let (c, m) := emitReg c m rt (c.r rs + simm); (c, m, .normal none)          -- ADDIU
  | 0x0A =>                                                                                -- SLTI
    let v : Word := if w2i (c.r rs) < w2i simm then 1 else 0
    let (c, m) := emitReg c m rt v; (c, m, .normal none)
  | 0x0B =>                                                                                -- SLTIU
    let v : Word := if (c.r rs).toNat < simm.toNat then 1 else 0
    let (c, m) := emitReg c m rt v; (c, m, .normal none)
  | 0x0C => let (c, m) := emitReg c m rt (c.r rs &&& BitVec.ofNat 32 imm); (c, m, .normal none) -- ANDI
  | 0x0D => let (c, m) := emitReg c m rt (c.r rs ||| BitVec.ofNat 32 imm); (c, m, .normal none) -- ORI
  | 0x0E => let (c, m) := emitReg c m rt (c.r rs ^^^ BitVec.ofNat 32 imm); (c, m, .normal none) -- XORI
  | 0x0F => let (c, m) := emitReg c m rt (BitVec.ofNat 32 (imm <<< 16)); (c, m, .normal none)   -- LUI
  | 0x10 =>  -- COP0
    if rs == 0x00 then  -- MFC0
      let v := c.c0 (rd, imm &&& 0x7)
      let (c, m) := emitReg c m rt v
      (c, m.emit (.cp15 "mfc0" rd 0 (imm &&& 7) 0 rt v), .normal none)
    else if rs == 0x04 then  -- MTC0
      let v := c.r rt
      let k := (rd, imm &&& 0x7)
      let c := c.setC0 k v
      let c := if k == COMPARE then c.setC0 CAUSE (c.c0 CAUSE &&& ~~~ bit 15) else c
      (c, m.emit (.cp15 "mtc0" rd 0 (imm &&& 7) 0 rt v), .normal none)
    else if rs == 0x10 then  -- CO: coprocessor operation
      if funct == 0x18 then  -- ERET
        let c := c.setC0 STATUS (c.c0 STATUS &&& ~~~ (2 : Word))
        let epc := c.c0 EPC
        (({ c with pc := epc, npc := epc + 4 }), m.emit (.exception "eret" epc 0), .eret)
      else if funct == 0x02 || funct == 0x06 then  -- TLBWI / TLBWR
        let vpn := (c.c0 ENTRYHI).toNat
        let pfn := ((c.c0 ENTRYLO).toNat >>> 6) <<< 12
        let c := c.addTlb vpn pfn
        (c, m.emit (.cp15 "tlbw" 10 0 2 0 0 (c.c0 ENTRYLO)), .normal none)
      else if funct == 0x01 then  -- TLBR: read TLB[INDEX] into EntryHi/EntryLo
        let idx := (c.c0 INDEX).toNat
        match c.tlb.drop idx with
        | (vpn, pfn) :: _ =>
          let c := c.setC0 ENTRYHI (BitVec.ofNat 32 vpn)
          let c := c.setC0 ENTRYLO (BitVec.ofNat 32 ((pfn >>> 12) <<< 6))
          (c, m.emit (.note "tlbr"), .normal none)
        | [] => (c, m.emit (.note "tlbr_miss"), .normal none)
      else if funct == 0x08 then  -- TLBP: probe TLB with EntryHi
        let vpn_page := (c.c0 ENTRYHI).toNat &&& 0xFFFFE000
        let (_, foundIdx) := c.tlb.foldl (fun (acc : Nat × Option Nat) entry =>
          let (i, res) := acc
          let hit := entry.1 / 0x1000 * 0x1000 == vpn_page
          (i + 1, if res.isSome then res else if hit then some i else none))
          (0, (none : Option Nat))
        match foundIdx with
        | some i => let c := c.setC0 INDEX (BitVec.ofNat 32 i)
                    (c, m.emit (.note "tlbp_hit"), .normal none)
        | none => let c := c.setC0 INDEX (0x80000000 : Word)
                  (c, m.emit (.note "tlbp_miss"), .normal none)
      else if funct == 0x20 then  -- WAIT: stall until interrupt
        (c, m.emit (.note "wait"), .normal none)
      else (c, m.emit (.note "cop0_unimpl"), .normal none)
    else (c, m, .normal none)
  | 0x1C =>  -- SPECIAL2
    match funct with
    | 0x00 =>  -- MADD: hi:lo += signed(rs) * signed(rt)
      let a := w2i (c.r rs); let b := w2i (c.r rt)
      let prod := a * b
      let prod_u64 := if prod < 0 then (prod + Int.ofNat (1 <<< 64)).toNat else prod.toNat
      let acc := (c.hi.toNat <<< 32) ||| c.lo.toNat
      let result := (prod_u64 + acc) &&& ((1 <<< 64) - 1)
      ({ c with lo := BitVec.ofNat 32 (result &&& 0xFFFFFFFF),
                hi := BitVec.ofNat 32 ((result >>> 32) &&& 0xFFFFFFFF) }, m, .normal none)
    | 0x01 =>  -- MADDU: hi:lo += unsigned(rs) * unsigned(rt)
      let prod := (c.r rs).toNat * (c.r rt).toNat
      let acc := (c.hi.toNat <<< 32) ||| c.lo.toNat
      let result := (prod + acc) &&& ((1 <<< 64) - 1)
      ({ c with lo := BitVec.ofNat 32 (result &&& 0xFFFFFFFF),
                hi := BitVec.ofNat 32 ((result >>> 32) &&& 0xFFFFFFFF) }, m, .normal none)
    | 0x02 =>  -- MUL: rd = low32(rs * rt); lower bits same for signed/unsigned
      let prod := (c.r rs).toNat * (c.r rt).toNat
      let (c, m) := emitReg c m rd (BitVec.ofNat 32 (prod &&& 0xFFFFFFFF))
      (c, m, .normal none)
    | 0x04 =>  -- MSUB: hi:lo -= signed(rs) * signed(rt)
      let a := w2i (c.r rs); let b := w2i (c.r rt)
      let prod := a * b
      let prod_u64 := if prod < 0 then (prod + Int.ofNat (1 <<< 64)).toNat else prod.toNat
      let acc := (c.hi.toNat <<< 32) ||| c.lo.toNat
      let result := (acc + (1 <<< 64) - prod_u64) &&& ((1 <<< 64) - 1)
      ({ c with lo := BitVec.ofNat 32 (result &&& 0xFFFFFFFF),
                hi := BitVec.ofNat 32 ((result >>> 32) &&& 0xFFFFFFFF) }, m, .normal none)
    | 0x05 =>  -- MSUBU: hi:lo -= unsigned(rs) * unsigned(rt)
      let prod := (c.r rs).toNat * (c.r rt).toNat
      let acc := (c.hi.toNat <<< 32) ||| c.lo.toNat
      let result := (acc + (1 <<< 64) - prod) &&& ((1 <<< 64) - 1)
      ({ c with lo := BitVec.ofNat 32 (result &&& 0xFFFFFFFF),
                hi := BitVec.ofNat 32 ((result >>> 32) &&& 0xFFFFFFFF) }, m, .normal none)
    | 0x20 =>  -- CLZ
      let (c, m) := emitReg c m rd (BitVec.ofNat 32 (clz32 (c.r rs).toNat))
      (c, m, .normal none)
    | 0x21 =>  -- CLO
      let (c, m) := emitReg c m rd (BitVec.ofNat 32 (clo32 (c.r rs).toNat))
      (c, m, .normal none)
    | 0x3F => let (c, m) := enterException c m EXC_BP none; (c, m, .exception)  -- SDBBP
    | _ => ({ c with halted := true }, m.emit (.note "reserved_special2"), .halt)
  | 0x1F =>  -- SPECIAL3 (MIPS32r2)
    match funct with
    | 0x00 =>  -- EXT: rt = ZeroExtend(rs[lsb + size - 1 : lsb])
      let pos := sa; let size := rd + 1
      if pos + size > 32 then
        ({ c with halted := true }, m.emit (.note "ext_unpredictable"), .halt)
      else
        let mask := if size == 32 then 0xFFFFFFFF else (1 <<< size) - 1
        let v := BitVec.ofNat 32 ((c.r rs).toNat >>> pos &&& mask)
        let (c, m) := emitReg c m rt v
        (c, m, .normal none)
    | 0x04 =>  -- INS: rt[msb:lsb] = rs[size-1:0]
      let pos := sa
      if rd < sa then
        ({ c with halted := true }, m.emit (.note "ins_unpredictable"), .halt)
      else
        let size := rd - sa + 1
        let mask := if size == 32 then 0xFFFFFFFF else (1 <<< size) - 1
        let rs_bits := (c.r rs).toNat &&& mask
        let shifted_mask := (mask <<< pos) &&& 0xFFFFFFFF
        let rt_cleared := (c.r rt).toNat &&& (shifted_mask ^^^ 0xFFFFFFFF)
        let v := BitVec.ofNat 32 (rt_cleared ||| (rs_bits <<< pos))
        let (c, m) := emitReg c m rt v
        (c, m, .normal none)
    | 0x20 =>  -- BSHFL
      match sa with
      | 0x02 =>  -- WSBH: swap bytes within each halfword of rt → rd
        let w := (c.r rt).toNat
        let lo_h := w &&& 0xFFFF
        let hi_h := (w >>> 16) &&& 0xFFFF
        let lo' := ((lo_h &&& 0xFF) <<< 8) ||| ((lo_h >>> 8) &&& 0xFF)
        let hi' := ((hi_h &&& 0xFF) <<< 8) ||| ((hi_h >>> 8) &&& 0xFF)
        let (c, m) := emitReg c m rd (BitVec.ofNat 32 ((hi' <<< 16) ||| lo'))
        (c, m, .normal none)
      | 0x10 =>  -- SEB: sign-extend byte rt[7:0] → rd
        let byte := (c.r rt).toNat &&& 0xFF
        let v := BitVec.ofNat 32 (if byte &&& 0x80 != 0 then byte ||| 0xFFFFFF00 else byte)
        let (c, m) := emitReg c m rd v; (c, m, .normal none)
      | 0x18 =>  -- SEH: sign-extend halfword rt[15:0] → rd
        let hw := (c.r rt).toNat &&& 0xFFFF
        let v := BitVec.ofNat 32 (if hw &&& 0x8000 != 0 then hw ||| 0xFFFF0000 else hw)
        let (c, m) := emitReg c m rd v; (c, m, .normal none)
      | _ => ({ c with halted := true }, m.emit (.note "reserved_bshfl"), .halt)
    | 0x3B =>  -- RDHWR: rt = HWR[rd] (returns Unicorn-compatible fixed values)
      let v := match rd with
        | 0  => BitVec.ofNat 32 0x3FF   -- CPUNum (Unicorn returns 0x3FF)
        | 1  => BitVec.ofNat 32 0x20    -- SYNCI_Step = 32 bytes
        | 2  => c.c0 COUNT              -- CC: cycle counter
        | 3  => BitVec.ofNat 32 0x2     -- CCRes
        | _  => BitVec.ofNat 32 0
      let (c, m) := emitReg c m rt v; (c, m, .normal none)
    | _ => ({ c with halted := true }, m.emit (.note "reserved_special3"), .halt)
  | 0x20 =>  -- LB: sign-extend byte
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p =>
      let aligned := BitVec.ofNat 32 (p.toNat &&& 0xFFFFFFFC)
      let (res, m) := m.busRead aligned 32
      match res with
      | .error _ => ({ c with halted := true }, m, .halt)
      | .ok w =>
        let byte := (w.toNat >>> ((p.toNat &&& 3) * 8)) &&& 0xFF
        let v := BitVec.ofNat 32 (if byte &&& 0x80 != 0 then byte ||| 0xFFFFFF00 else byte)
        let (c, m) := emitReg c m rt v; (c, m, .normal none)
  | 0x21 =>  -- LH: sign-extend halfword (address bit 1 selects low or high halfword)
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p =>
      let aligned := BitVec.ofNat 32 (p.toNat &&& 0xFFFFFFFC)
      let (res, m) := m.busRead aligned 32
      match res with
      | .error _ => ({ c with halted := true }, m, .halt)
      | .ok w =>
        let hw := (w.toNat >>> ((p.toNat &&& 2) * 8)) &&& 0xFFFF
        let v := BitVec.ofNat 32 (if hw &&& 0x8000 != 0 then hw ||| 0xFFFF0000 else hw)
        let (c, m) := emitReg c m rt v; (c, m, .normal none)
  | 0x22 =>  -- LWL (LE): merge (byteOff+1) bytes from mem[byteOff*8+7..0] into rt[byteOff*8+7..0]
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p =>
      let aligned := BitVec.ofNat 32 (p.toNat &&& 0xFFFFFFFC)
      let byteOff := p.toNat &&& 3
      let (res, m) := m.busRead aligned 32
      match res with
      | .error _ => ({ c with halted := true }, m, .halt)
      | .ok w =>
        -- LE LWL: low (byteOff+1) bytes of aligned word → high (byteOff+1) bytes of rt
        let nbytes := byteOff + 1
        let shift := (3 - byteOff) * 8
        let src_mask := (1 <<< (nbytes * 8)) - 1
        let rt_mask := (src_mask <<< shift) &&& 0xFFFFFFFF
        let v := BitVec.ofNat 32 ((c.r rt).toNat &&& (rt_mask ^^^ 0xFFFFFFFF) ||| ((w.toNat &&& src_mask) <<< shift))
        let (c, m) := emitReg c m rt v; (c, m, .normal none)
  | 0x24 =>  -- LBU: zero-extend byte
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p =>
      let aligned := BitVec.ofNat 32 (p.toNat &&& 0xFFFFFFFC)
      let (res, m) := m.busRead aligned 32
      match res with
      | .error _ => ({ c with halted := true }, m, .halt)
      | .ok w =>
        let v := BitVec.ofNat 32 ((w.toNat >>> ((p.toNat &&& 3) * 8)) &&& 0xFF)
        let (c, m) := emitReg c m rt v; (c, m, .normal none)
  | 0x25 =>  -- LHU: zero-extend halfword
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p =>
      let aligned := BitVec.ofNat 32 (p.toNat &&& 0xFFFFFFFC)
      let (res, m) := m.busRead aligned 32
      match res with
      | .error _ => ({ c with halted := true }, m, .halt)
      | .ok w =>
        let v := BitVec.ofNat 32 ((w.toNat >>> ((p.toNat &&& 2) * 8)) &&& 0xFFFF)
        let (c, m) := emitReg c m rt v; (c, m, .normal none)
  | 0x26 =>  -- LWR (LE): merge bytes from mem[31..byteOff*8] into rt[31..byteOff*8]
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p =>
      let aligned := BitVec.ofNat 32 (p.toNat &&& 0xFFFFFFFC)
      let byteOff := p.toNat &&& 3
      let (res, m) := m.busRead aligned 32
      match res with
      | .error _ => ({ c with halted := true }, m, .halt)
      | .ok w =>
        -- LE LWR: high (4-byteOff) bytes of aligned word shifted right → low (4-byteOff) bytes of rt
        let shift := byteOff * 8
        let dst_mask := (1 <<< ((4 - byteOff) * 8)) - 1
        let v := BitVec.ofNat 32 ((c.r rt).toNat &&& (dst_mask ^^^ 0xFFFFFFFF) ||| ((w.toNat >>> shift) &&& dst_mask))
        let (c, m) := emitReg c m rt v; (c, m, .normal none)
  | 0x23 =>  -- LW
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p => let (res, m) := m.busRead p 32
                match res with
                | .ok v => let (c, m) := emitReg c m rt v; (c, m, .normal none)
                | .error _ => ({ c with halted := true }, m, .halt)
  | 0x28 =>  -- SB: store byte (read-modify-write)
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p =>
      let aligned := BitVec.ofNat 32 (p.toNat &&& 0xFFFFFFFC)
      let shift := (p.toNat &&& 3) * 8
      let (rres, m) := m.busRead aligned 32
      match rres with
      | .error _ => ({ c with halted := true }, m, .halt)
      | .ok w =>
        let mask := 0xFF <<< shift
        let new_w := BitVec.ofNat 32 ((w.toNat &&& (mask ^^^ 0xFFFFFFFF)) ||| (((c.r rt).toNat &&& 0xFF) <<< shift))
        let (wres, m) := m.busWrite aligned new_w 32
        match wres with
        | .ok _ => (c, m, .normal none)
        | .error _ => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x29 =>  -- SH: store halfword (read-modify-write)
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p =>
      let aligned := BitVec.ofNat 32 (p.toNat &&& 0xFFFFFFFC)
      let shift := (p.toNat &&& 2) * 8
      let (rres, m) := m.busRead aligned 32
      match rres with
      | .error _ => ({ c with halted := true }, m, .halt)
      | .ok w =>
        let mask := 0xFFFF <<< shift
        let new_w := BitVec.ofNat 32 ((w.toNat &&& (mask ^^^ 0xFFFFFFFF)) ||| (((c.r rt).toNat &&& 0xFFFF) <<< shift))
        let (wres, m) := m.busWrite aligned new_w 32
        match wres with
        | .ok _ => (c, m, .normal none)
        | .error _ => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x2A =>  -- SWL (LE): store low (byteOff+1) bytes of rt into mem[byteOff*8+7..0]
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p =>
      let aligned := BitVec.ofNat 32 (p.toNat &&& 0xFFFFFFFC)
      let byteOff := p.toNat &&& 3
      let (rres, m) := m.busRead aligned 32
      match rres with
      | .error _ => ({ c with halted := true }, m, .halt)
      | .ok w =>
        -- LE SWL: high (byteOff+1) bytes of rt shifted down → low (byteOff+1) bytes of mem
        let nbytes := byteOff + 1
        let shift := (3 - byteOff) * 8
        let mask := (1 <<< (nbytes * 8)) - 1
        let rt_shifted := (c.r rt).toNat >>> shift
        let new_w := BitVec.ofNat 32 ((w.toNat &&& (mask ^^^ 0xFFFFFFFF)) ||| (rt_shifted &&& mask))
        let (wres, m) := m.busWrite aligned new_w 32
        match wres with
        | .ok _ => (c, m, .normal none)
        | .error _ => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x2B =>  -- SW
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p =>
      let (res, m) := m.busWrite p (c.r rt) 32
      match res with
      | .ok _ => (c, m, .normal none)
      | .error _ => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x2E =>  -- SWR (LE): store high (4-byteOff) bytes of rt into mem[31..byteOff*8]
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p =>
      let aligned := BitVec.ofNat 32 (p.toNat &&& 0xFFFFFFFC)
      let byteOff := p.toNat &&& 3
      let (rres, m) := m.busRead aligned 32
      match rres with
      | .error _ => ({ c with halted := true }, m, .halt)
      | .ok w =>
        -- LE SWR: low (4-byteOff) bytes of rt shifted left → high (4-byteOff) bytes of mem
        let shift := byteOff * 8
        let mask := if shift == 0 then 0xFFFFFFFF else (0xFFFFFFFF <<< shift) &&& 0xFFFFFFFF
        let rt_shifted := ((c.r rt).toNat <<< shift) &&& 0xFFFFFFFF
        let new_w := BitVec.ofNat 32 ((w.toNat &&& (mask ^^^ 0xFFFFFFFF)) ||| rt_shifted)
        let (wres, m) := m.busWrite aligned new_w 32
        match wres with
        | .ok _ => (c, m, .normal none)
        | .error _ => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x30 =>  -- LL: load linked (sets llbit)
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p =>
      let (res, m) := m.busRead p 32
      match res with
      | .ok v =>
        let c := { c with llbit := true }
        let (c, m) := emitReg c m rt v; (c, m, .normal none)
      | .error _ => ({ c with halted := true }, m, .halt)
  | 0x38 =>  -- SC: store conditional (succeeds iff llbit set)
    if !c.llbit then
      let (c, m) := emitReg c m rt 0; (c, m, .normal none)   -- SC fails
    else
      let vaddr := c.r rs + simm
      match c.translate vaddr with
      | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
      | some p =>
        let (res, m) := m.busWrite p (c.r rt) 32
        match res with
        | .ok _ =>
          let c := { c with llbit := false }
          let (c, m) := emitReg c m rt 1; (c, m, .normal none)  -- SC succeeds
        | .error _ => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x2F => (c, m, .normal none)  -- CACHE: cache operations (NOP in simulation)
  | 0x33 => (c, m, .normal none)  -- PREF: prefetch hint (NOP in simulation)
  | 0x11 =>  -- COP1 (floating-point coprocessor)
    let fmt := rs
    if fmt == 0x00 then  -- MFC1: GPR[rt] = FPR[rd]
      let (c, m) := emitReg c m rt (c.fr rd); (c, m, .normal none)
    else if fmt == 0x02 then  -- CFC1: GPR[rt] = FCR[rd]
      let v := if rd == 31 then c.fcr31 else BitVec.ofNat 32 0
      let (c, m) := emitReg c m rt v; (c, m, .normal none)
    else if fmt == 0x03 then  -- MFHC1: GPR[rt] = high word of FPR pair (FPR[rd+1])
      let (c, m) := emitReg c m rt (c.fr (rd + 1)); (c, m, .normal none)
    else if fmt == 0x04 then  -- MTC1: FPR[rd] = GPR[rt]
      let c := { c with fprs := c.fprs.setIfInBounds rd (c.r rt) }
      (c, m, .normal none)
    else if fmt == 0x06 then  -- CTC1: FCR[rd] = GPR[rt]
      let c := if rd == 31 then { c with fcr31 := c.r rt } else c
      (c, m, .normal none)
    else if fmt == 0x07 then  -- MTHC1: high word of FPR pair (FPR[rd+1]) = GPR[rt]
      let c := { c with fprs := c.fprs.setIfInBounds (rd + 1) (c.r rt) }
      (c, m, .normal none)
    else if fmt == 0x08 then  -- BC1F/BC1T/BC1FL/BC1TL
      let cc := (rt >>> 2) &&& 7
      let nd := (rt >>> 1) &&& 1
      let tf := rt &&& 1
      let fpos := fccPos cc
      let fccVal := (c.fcr31.toNat >>> fpos) &&& 1
      let taken := if tf == 0 then fccVal == 0 else fccVal == 1
      let target := pc + 4 + simm * 4
      if nd == 0 then (c, m, .normal (if taken then some target else none))
      else (c, m, .normalLikely (if taken then some target else none))
    else if fmt == 0x10 || fmt == 0x11 then  -- S (0x10) or D (0x11) format
      let isD := fmt == 0x11
      let floatFmt := if isD then Sei.Float.Fmt.f64 else Sei.Float.Fmt.f32
      let fsV := if isD then c.frD rd else (c.fr rd).toNat
      let ftV := if isD then c.frD rt else (c.fr rt).toNat
      let fdI := sa
      let signBit := if isD then 63 else 31
      let allBits := if isD then 0xFFFFFFFFFFFFFFFF else 0xFFFFFFFF
      match funct with
      | 0x00 => (writeFpr c fdI isD (Sei.Float.addSub floatFmt fsV ftV false), m, .normal none)
      | 0x01 => (writeFpr c fdI isD (Sei.Float.addSub floatFmt fsV ftV true), m, .normal none)
      | 0x02 => (writeFpr c fdI isD (Sei.Float.mul floatFmt fsV ftV), m, .normal none)
      | 0x03 => (writeFpr c fdI isD (Sei.Float.div floatFmt fsV ftV), m, .normal none)
      | 0x04 => (writeFpr c fdI isD (Sei.Float.sqrt floatFmt fsV), m, .normal none)
      | 0x05 => (writeFpr c fdI isD (fsV &&& (allBits ^^^ (1 <<< signBit))), m, .normal none)
      | 0x06 => (writeFpr c fdI isD fsV, m, .normal none)
      | 0x07 => (writeFpr c fdI isD (fsV ^^^ (1 <<< signBit)), m, .normal none)
      | 0x0C =>
        let v := Sei.Float.fToInt floatFmt true true fsV
        ({ c with fprs := c.fprs.setIfInBounds fdI (BitVec.ofNat 32 (v &&& 0xFFFFFFFF)) }, m, .normal none)
      | 0x0D =>
        let v := Sei.Float.fToInt floatFmt true false fsV
        ({ c with fprs := c.fprs.setIfInBounds fdI (BitVec.ofNat 32 (v &&& 0xFFFFFFFF)) }, m, .normal none)
      | 0x0E =>
        let v := ceilW floatFmt fsV
        ({ c with fprs := c.fprs.setIfInBounds fdI (BitVec.ofNat 32 (v &&& 0xFFFFFFFF)) }, m, .normal none)
      | 0x0F =>
        let v := floorW floatFmt fsV
        ({ c with fprs := c.fprs.setIfInBounds fdI (BitVec.ofNat 32 (v &&& 0xFFFFFFFF)) }, m, .normal none)
      | 0x11 =>  -- MOVCF: if FCC[cc]==tf then FPR[fd]=FPR[fs]
        let cc2 := (rt >>> 2) &&& 7; let tf2 := rt &&& 1
        let fpos := fccPos cc2
        let fccVal := (c.fcr31.toNat >>> fpos) &&& 1
        if (if tf2 == 0 then fccVal == 0 else fccVal == 1) then
          (writeFpr c fdI isD fsV, m, .normal none)
        else (c, m, .normal none)
      | 0x12 =>  -- MOVZ.fmt: if GPR[rt]==0 then FPR[fd]=FPR[fs]
        if c.r rt == 0 then (writeFpr c fdI isD fsV, m, .normal none) else (c, m, .normal none)
      | 0x13 =>  -- MOVN.fmt: if GPR[rt]!=0 then FPR[fd]=FPR[fs]
        if c.r rt != 0 then (writeFpr c fdI isD fsV, m, .normal none) else (c, m, .normal none)
      | 0x20 =>  -- CVT.S: D→S or S nop
        let v := if isD then Sei.Float.f64ToF32 fsV else fsV
        ({ c with fprs := c.fprs.setIfInBounds fdI (BitVec.ofNat 32 (v &&& 0xFFFFFFFF)) }, m, .normal none)
      | 0x21 =>  -- CVT.D: S→D or D nop
        let v := if isD then fsV else Sei.Float.f32ToF64 fsV
        (c.setFrD fdI v, m, .normal none)
      | 0x24 =>  -- CVT.W: float→word (RNE)
        let v := Sei.Float.fToInt floatFmt true true fsV
        ({ c with fprs := c.fprs.setIfInBounds fdI (BitVec.ofNat 32 (v &&& 0xFFFFFFFF)) }, m, .normal none)
      | _ =>  -- C.cond.fmt: funct 0x30..0x3F
        if funct &&& 0x30 == 0x30 then
          let cond := funct &&& 0xF
          let cc3 := (sa >>> 2) &&& 7
          let nzcv := Sei.Float.cmp floatFmt fsV ftV
          let lt := nzcv &&& 8 != 0; let eq := nzcv &&& 4 != 0; let un := nzcv &&& 1 != 0
          let condResult := match cond with
            | 0 => false | 1 => un | 2 => eq | 3 => eq || un
            | 4 => lt | 5 => lt || un | 6 => lt || eq | 7 => lt || eq || un
            | 8 => false | 9 => un | 10 => eq | 11 => eq || un
            | 12 => lt | 13 => lt || un | 14 => lt || eq | _ => lt || eq || un
          let fpos := fccPos cc3
          let newFcr31 := if condResult
            then c.fcr31 ||| BitVec.ofNat 32 (1 <<< fpos)
            else c.fcr31 &&& ~~~ BitVec.ofNat 32 (1 <<< fpos)
          ({ c with fcr31 := newFcr31 }, m, .normal none)
        else (c, m, .normal none)
    else if fmt == 0x14 then  -- W format: integer→float conversions
      let intV := (c.fr rd).toNat
      let fdI := sa
      match funct with
      | 0x20 =>  -- CVT.S.W: word→single
        let v := Sei.Float.i32ToF Sei.Float.Fmt.f32 intV
        ({ c with fprs := c.fprs.setIfInBounds fdI (BitVec.ofNat 32 (v &&& 0xFFFFFFFF)) }, m, .normal none)
      | 0x21 =>  -- CVT.D.W: word→double
        let v := Sei.Float.i32ToF Sei.Float.Fmt.f64 intV
        (c.setFrD fdI v, m, .normal none)
      | _ => (c, m, .normal none)
    else (c, m, .normal none)
  | 0x31 =>  -- LWC1: FPR[rt] = MEM[rs+offset]
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p =>
      let (res, m) := m.busRead p 32
      match res with
      | .ok v => let c := { c with fprs := c.fprs.setIfInBounds rt v }
                 (c, m, .normal none)
      | .error _ => ({ c with halted := true }, m, .halt)
  | 0x35 =>  -- LDC1: FPR[rt]:FPR[rt+1] = MEM[rs+offset] (LE: lo word first)
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p =>
      let (r0, m) := m.busRead p 32
      let (r1, m) := m.busRead (p + 4) 32
      match r0, r1 with
      | .ok lo, .ok hi =>
        let c := { c with fprs := (c.fprs.setIfInBounds rt lo).setIfInBounds (rt + 1) hi }
        (c, m, .normal none)
      | _, _ => ({ c with halted := true }, m, .halt)
  | 0x39 =>  -- SWC1: MEM[rs+offset] = FPR[rt]
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p =>
      let (res, m) := m.busWrite p (c.fr rt) 32
      match res with
      | .ok _ => (c, m, .normal none)
      | .error _ => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x3D =>  -- SDC1: MEM[rs+offset]:+4 = FPR[rt]:FPR[rt+1]
    let vaddr := c.r rs + simm
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p =>
      let (r0, m) := m.busWrite p (c.fr rt) 32
      let (r1, m) := m.busWrite (p + 4) (c.fr (rt + 1)) 32
      match r0, r1 with
      | .ok _, .ok _ => (c, m, .normal none)
      | _, _ => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x13 =>  -- COP1X: indexed FP loads/stores and FP-MAC
    match funct with
    | 0x00 =>  -- LWXC1: FPR[sa] = MEM32[GPR[rs]+GPR[rt]]
      let vaddr := c.r rs + c.r rt
      match c.translate vaddr with
      | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
      | some p =>
        match m.busRead p 32 with
        | (.ok v, m) => let c := { c with fprs := c.fprs.setIfInBounds sa v }; (c, m, .normal none)
        | (_, m) => ({ c with halted := true }, m, .halt)
    | 0x01 =>  -- LDXC1: FPR[sa]:FPR[sa+1] = MEM64[GPR[rs]+GPR[rt]]
      let vaddr := c.r rs + c.r rt
      match c.translate vaddr with
      | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
      | some p =>
        let (r0, m) := m.busRead p 32
        let (r1, m) := m.busRead (p + 4) 32
        match r0, r1 with
        | .ok lo, .ok hi =>
          let c := { c with fprs := (c.fprs.setIfInBounds sa lo).setIfInBounds (sa + 1) hi }
          (c, m, .normal none)
        | _, _ => ({ c with halted := true }, m, .halt)
    | 0x08 =>  -- SWXC1: MEM32[GPR[rs]+GPR[rt]] = FPR[rd]
      let vaddr := c.r rs + c.r rt
      match c.translate vaddr with
      | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
      | some p =>
        match m.busWrite p (c.fr rd) 32 with
        | (.ok _, m) => (c, m, .normal none)
        | (_, m) => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | 0x09 =>  -- SDXC1: MEM64[GPR[rs]+GPR[rt]] = FPR[rd]:FPR[rd+1]
      let vaddr := c.r rs + c.r rt
      match c.translate vaddr with
      | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
      | some p =>
        let (r0, m) := m.busWrite p (c.fr rd) 32
        let (r1, m) := m.busWrite (p + 4) (c.fr (rd + 1)) 32
        match r0, r1 with
        | .ok _, .ok _ => (c, m, .normal none)
        | _, _ => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | 0x0F => (c, m, .normal none)  -- PREFX: NOP
    | 0x20 =>  -- MADD.S: FPR[sa] = FPR[rs]*FPR[rt] + FPR[rd]
      let prod := Sei.Float.mul .f32 (c.fr rs).toNat (c.fr rt).toNat
      let result := Sei.Float.addSub .f32 prod (c.fr rd).toNat false
      let c := { c with fprs := c.fprs.setIfInBounds sa (BitVec.ofNat 32 (result &&& 0xFFFFFFFF)) }
      (c, m, .normal none)
    | 0x21 =>  -- MADD.D: FPR[sa] = FPR[rs]*FPR[rt] + FPR[rd] (double)
      let prod := Sei.Float.mul .f64 (c.frD rs) (c.frD rt)
      let result := Sei.Float.addSub .f64 prod (c.frD rd) false
      (c.setFrD sa result, m, .normal none)
    | 0x28 =>  -- MSUB.S: FPR[sa] = FPR[rs]*FPR[rt] - FPR[rd]
      let prod := Sei.Float.mul .f32 (c.fr rs).toNat (c.fr rt).toNat
      let result := Sei.Float.addSub .f32 prod (c.fr rd).toNat true
      let c := { c with fprs := c.fprs.setIfInBounds sa (BitVec.ofNat 32 (result &&& 0xFFFFFFFF)) }
      (c, m, .normal none)
    | 0x29 =>  -- MSUB.D: FPR[sa] = FPR[rs]*FPR[rt] - FPR[rd] (double)
      let prod := Sei.Float.mul .f64 (c.frD rs) (c.frD rt)
      let result := Sei.Float.addSub .f64 prod (c.frD rd) true
      (c.setFrD sa result, m, .normal none)
    | 0x30 =>  -- NMADD.S: FPR[sa] = -(FPR[rs]*FPR[rt] + FPR[rd])
      let prod := Sei.Float.mul .f32 (c.fr rs).toNat (c.fr rt).toNat
      let result := (Sei.Float.addSub .f32 prod (c.fr rd).toNat false) ^^^ 0x80000000
      let c := { c with fprs := c.fprs.setIfInBounds sa (BitVec.ofNat 32 (result &&& 0xFFFFFFFF)) }
      (c, m, .normal none)
    | 0x31 =>  -- NMADD.D: FPR[sa] = -(FPR[rs]*FPR[rt] + FPR[rd]) (double)
      let prod := Sei.Float.mul .f64 (c.frD rs) (c.frD rt)
      let result := (Sei.Float.addSub .f64 prod (c.frD rd) false) ^^^ 0x80000000_00000000
      (c.setFrD sa result, m, .normal none)
    | 0x38 =>  -- NMSUB.S: FPR[sa] = -(FPR[rs]*FPR[rt] - FPR[rd])
      let prod := Sei.Float.mul .f32 (c.fr rs).toNat (c.fr rt).toNat
      let result := (Sei.Float.addSub .f32 prod (c.fr rd).toNat true) ^^^ 0x80000000
      let c := { c with fprs := c.fprs.setIfInBounds sa (BitVec.ofNat 32 (result &&& 0xFFFFFFFF)) }
      (c, m, .normal none)
    | 0x39 =>  -- NMSUB.D: FPR[sa] = -(FPR[rs]*FPR[rt] - FPR[rd]) (double)
      let prod := Sei.Float.mul .f64 (c.frD rs) (c.frD rt)
      let result := (Sei.Float.addSub .f64 prod (c.frD rd) true) ^^^ 0x80000000_00000000
      (c.setFrD sa result, m, .normal none)
    | _ => ({ c with halted := true }, m.emit (.unsupported pc funct "cop1x_funct"), .halt)
  | 0x1D =>  -- JALX: jump-and-link, switch to MIPS16e mode (bit 0 of npc = ISA mode bit)
    let instrIdx := (rs <<< 21) ||| (rt <<< 16) ||| imm
    let target := BitVec.ofNat 32 (((pc.toNat &&& 0xF0000000) ||| (instrIdx <<< 2)) ||| 1)
    let (c, m) := emitReg c m 31 (pc + 8)  -- link $ra = PC+8 (in MIPS32 mode)
    (c, m, .normal (some target))  -- delay slot runs in MIPS32, then jump to target|1
  | _ => ({ c with halted := true }, m.emit (.unsupported pc op "mips_reserved"), .halt)

/-! ### MIPS16e instruction set -/

-- MIPS16e 3-bit register map → GPR index
private def rx16 (r3 : Nat) : Nat :=
  match r3 with
  | 0 => 16 | 1 => 17 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | _ => 7

-- T register ($t8 = $24)
private def tReg16 : Nat := 24

-- Execute a single MIPS16e instruction (already identified, may be EXTEND-prefixed).
-- pc: virtual PC of the instruction (bit0=1 for MIPS16e mode).
-- hw: the base 16-bit halfword value.
-- extImm: SignExt((ext11<<5)|base[4:0],16) — for arithmetic/branch/ADJSP with EXTEND.
-- extOff: SignExt(ext11,11) — byte offset for load/store with EXTEND.
-- isExt: whether EXTEND prefix was present.
private def execute16 (c : Cpu) (m : Machine) (pc : Word) (hw : Nat)
    (extImm : Int) (extOff : Int) (isExt : Bool) : Cpu × Machine × Ctl :=
  let op5 := (hw >>> 11) &&& 0x1f
  let rx3 := (hw >>> 8) &&& 7;  let ry3 := (hw >>> 5) &&& 7
  let rx := rx16 rx3;  let ry := rx16 ry3
  let imm8 := hw &&& 0xFF;  let imm5 := hw &&& 0x1F
  let imm11 := hw &&& 0x7FF;  let i8op := (hw >>> 8) &&& 7
  let simm8 : Int := if imm8 &&& 0x80 != 0 then Int.ofNat imm8 - 256 else Int.ofNat imm8
  let simm11 : Int := if imm11 &&& 0x400 != 0 then Int.ofNat imm11 - 0x800 else Int.ofNat imm11
  let physPc := pc &&& (BitVec.ofNat 32 0xFFFFFFFE)
  match op5 with
  | 0x00 =>  -- ADDIU.SP: rx = $sp + (EXTEND: extImm else imm8*4)
    let off : Word := if isExt then i2w extImm else BitVec.ofNat 32 (imm8 * 4)
    let (c, m) := emitReg c m rx (c.r 29 + off); (c, m, .normalLikely none)
  | 0x01 =>  -- ADDIU.PC: rx = (pc&~3) + imm8*4
    let base : Word := physPc &&& (BitVec.ofNat 32 0xFFFFFFFC)
    let (c, m) := emitReg c m rx (base + BitVec.ofNat 32 (imm8 * 4)); (c, m, .normalLikely none)
  | 0x02 =>  -- B: unconditional branch (no delay slot)
    let off : Int := if isExt then extImm else simm11
    let tgt := BitVec.ofInt 32 (Int.ofNat (physPc.toNat + 2) + off * 2) ||| 1
    (c, m, .normalLikely (some tgt))
  | 0x04 =>  -- BEQZ: branch if rx == 0 (no delay slot)
    let off : Int := if isExt then extImm else simm8
    if c.r rx == 0 then
      let tgt := BitVec.ofInt 32 (Int.ofNat (physPc.toNat + 2) + off * 2) ||| 1
      (c, m, .normalLikely (some tgt))
    else (c, m, .normalLikely none)
  | 0x05 =>  -- BNEZ: branch if rx != 0 (no delay slot)
    let off : Int := if isExt then extImm else simm8
    if c.r rx != 0 then
      let tgt := BitVec.ofInt 32 (Int.ofNat (physPc.toNat + 2) + off * 2) ||| 1
      (c, m, .normalLikely (some tgt))
    else (c, m, .normalLikely none)
  | 0x06 =>  -- SHIFT: rx = op(ry, sa)
    let sa3 := (hw >>> 2) &&& 7
    let saVal := if isExt then imm5 else (if sa3 == 0 then 8 else sa3)
    let v := (c.r ry).toNat
    let result : Nat := match hw &&& 3 with
      | 0 => (v <<< saVal) &&& 0xFFFFFFFF
      | 2 => v >>> saVal
      | 3 => sar32 v saVal
      | _ => v
    let (c, m) := emitReg c m rx (BitVec.ofNat 32 result); (c, m, .normalLikely none)
  | 0x09 =>  -- ADDIU: rx += (EXTEND: extImm else simm8)
    let imm : Word := if isExt then i2w extImm else i2w simm8
    let (c, m) := emitReg c m rx (c.r rx + imm); (c, m, .normalLikely none)
  | 0x0A =>  -- SLTI: T = (rx < imm8) ? 1 : 0 (signed)
    let imm : Int := if isExt then extImm else simm8
    let result : Nat := if BitVec.slt (c.r rx) (i2w imm) then 1 else 0
    let (c, m) := emitReg c m tReg16 (BitVec.ofNat 32 result); (c, m, .normalLikely none)
  | 0x0B =>  -- SLTIU: T = (rx <u ZeroExt(imm8)) ? 1 : 0
    let imm : Nat := if isExt then (i2w extImm).toNat else imm8
    let result : Nat := if (c.r rx).toNat < imm then 1 else 0
    let (c, m) := emitReg c m tReg16 (BitVec.ofNat 32 result); (c, m, .normalLikely none)
  | 0x0C =>  -- I8: sub-operations via i8op
    match i8op with
    | 0 =>  -- BTEQZ: branch if T==0 (no delay slot)
      let off : Int := if isExt then extImm else simm8
      if c.r tReg16 == 0 then
        (c, m, .normalLikely (some (BitVec.ofInt 32 (Int.ofNat (physPc.toNat + 2) + off * 2) ||| 1)))
      else (c, m, .normalLikely none)
    | 1 =>  -- BTNEZ: branch if T!=0 (no delay slot)
      let off : Int := if isExt then extImm else simm8
      if c.r tReg16 != 0 then
        (c, m, .normalLikely (some (BitVec.ofInt 32 (Int.ofNat (physPc.toNat + 2) + off * 2) ||| 1)))
      else (c, m, .normalLikely none)
    | 2 =>  -- SWRASP: MEM32[sp + (EXTEND: extImm else imm8*4)] = $ra
      let off : Word := if isExt then i2w extImm else BitVec.ofNat 32 (imm8 * 4)
      let vaddr := c.r 29 + off
      match c.translate vaddr with
      | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
      | some p => match m.busWrite p (c.r 31) 32 with
        | (.ok _, m) => (c, m, .normalLikely none)
        | (_, m) => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | 3 =>  -- ADJSP: $sp += (EXTEND: extImm else 8*simm8)
      let adj : Word := if isExt then i2w extImm else i2w (simm8 * 8)
      let (c, m) := emitReg c m 29 (c.r 29 + adj); (c, m, .normalLikely none)
    | 4 =>  -- SAVE/RESTORE: simplified (adjust sp only; register save NOP for now)
      let isSave := imm8 &&& 0x80 != 0
      let fs7 := imm8 &&& 0x7F
      let rawSize : Nat := if isExt then (i2w extImm).toNat
                          else if fs7 == 0 then 128 else fs7 * 8
      let frameSize : Word := BitVec.ofNat 32 rawSize
      if isSave then
        let (c, m) := emitReg c m 29 (c.r 29 - frameSize); (c, m, .normalLikely none)
      else  -- RESTORE: adjust sp and jump to $ra (return)
        let newSp := c.r 29 + frameSize
        let c := { c with regs := c.regs.setIfInBounds 29 newSp }
        (c, m, .normalLikely (some (c.r 31)))
    | 5 =>  -- MOV32R: any GPR[r32] = rx16
      let r32 := ((hw &&& 0x18) <<< 0) ||| ry3  -- bits[4:3] upper, bits[7:5] as ry3 lower
      -- Actually: r32dest = {bits[4:3], bits[2:0]} but layout varies; use {(hw>>3)&3, ry3}
      let r32dest := (((hw >>> 3) &&& 3) <<< 3) ||| ry3
      let (c, m) := emitReg c m r32dest (c.r rx); (c, m, .normalLikely none)
    | 7 =>  -- MOVR32: rx16 = any GPR[r32src]
      let r32src := hw &&& 0x1f  -- bits[4:0]
      let (c, m) := emitReg c m rx (c.r r32src); (c, m, .normalLikely none)
    | _ => ({ c with halted := true }, m.emit (.unsupported pc i8op "mips16_i8op"), .halt)
  | 0x0D =>  -- LI: rx = (EXTEND: extImm else ZeroExt(imm8))
    let imm : Word := if isExt then i2w extImm else BitVec.ofNat 32 imm8
    let (c, m) := emitReg c m rx imm; (c, m, .normalLikely none)
  | 0x0E =>  -- CMPI: T = rx XOR (EXTEND: extImm else ZeroExt(imm8))
    let imm : Word := if isExt then i2w extImm else BitVec.ofNat 32 imm8
    let (c, m) := emitReg c m tReg16 (c.r rx ^^^ imm); (c, m, .normalLikely none)
  | 0x10 =>  -- LB: rx = SignExt8(MEM8[ry + off])
    let off : Word := if isExt then i2w extOff else (BitVec.ofNat 5 imm5).signExtend 32
    let vaddr := c.r ry + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p => match m.busRead p 8 with
      | (.ok v, m) => let (c, m) := emitReg c m rx ((BitVec.ofNat 8 v.toNat).signExtend 32); (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
  | 0x11 =>  -- LH: rx = SignExt16(MEM16[ry + off])
    let off : Word := if isExt then i2w extOff else BitVec.ofNat 32 (imm5 * 2)
    let vaddr := c.r ry + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p => match m.busRead p 16 with
      | (.ok v, m) => let (c, m) := emitReg c m rx ((BitVec.ofNat 16 v.toNat).signExtend 32); (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
  | 0x12 =>  -- LWSP: rx = MEM32[$sp + off]
    let off : Word := if isExt then i2w extOff else BitVec.ofNat 32 (imm8 * 4)
    let vaddr := c.r 29 + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p => match m.busRead p 32 with
      | (.ok v, m) => let (c, m) := emitReg c m rx v; (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
  | 0x13 =>  -- LW: rx = MEM32[ry + off]
    let off : Word := if isExt then i2w extOff else BitVec.ofNat 32 (imm5 * 4)
    let vaddr := c.r ry + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p => match m.busRead p 32 with
      | (.ok v, m) => let (c, m) := emitReg c m rx v; (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
  | 0x14 =>  -- LBU: rx = ZeroExt8(MEM8[ry + off])
    let off : Word := if isExt then i2w extOff else BitVec.ofNat 32 imm5
    let vaddr := c.r ry + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p => match m.busRead p 8 with
      | (.ok v, m) => let (c, m) := emitReg c m rx (BitVec.ofNat 32 v.toNat); (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
  | 0x15 =>  -- LHU: rx = ZeroExt16(MEM16[ry + off])
    let off : Word := if isExt then i2w extOff else BitVec.ofNat 32 (imm5 * 2)
    let vaddr := c.r ry + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p => match m.busRead p 16 with
      | (.ok v, m) => let (c, m) := emitReg c m rx (BitVec.ofNat 32 v.toNat); (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
  | 0x16 =>  -- LWPC: rx = MEM32[(physPc&~3) + off]
    let base : Word := physPc &&& (BitVec.ofNat 32 0xFFFFFFFC)
    let off : Word := if isExt then i2w extOff else BitVec.ofNat 32 (imm8 * 4)
    let vaddr := base + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
    | some p => match m.busRead p 32 with
      | (.ok v, m) => let (c, m) := emitReg c m rx v; (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBL (some vaddr); (c, m, .exception)
  | 0x18 =>  -- SB: MEM8[ry + off] = rx
    let off : Word := if isExt then i2w extOff else BitVec.ofNat 32 imm5
    let vaddr := c.r ry + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p => match m.busWrite p (c.r rx) 8 with
      | (.ok _, m) => (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x19 =>  -- SH: MEM16[ry + off] = rx
    let off : Word := if isExt then i2w extOff else BitVec.ofNat 32 (imm5 * 2)
    let vaddr := c.r ry + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p => match m.busWrite p (c.r rx) 16 with
      | (.ok _, m) => (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x1A =>  -- SWSP: MEM32[$sp + off] = rx
    let off : Word := if isExt then i2w extOff else BitVec.ofNat 32 (imm8 * 4)
    let vaddr := c.r 29 + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p => match m.busWrite p (c.r rx) 32 with
      | (.ok _, m) => (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x1B =>  -- SW: MEM32[ry + off] = rx
    let off : Word := if isExt then i2w extOff else BitVec.ofNat 32 (imm5 * 4)
    let vaddr := c.r ry + off
    match c.translate vaddr with
    | none => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
    | some p => match m.busWrite p (c.r rx) 32 with
      | (.ok _, m) => (c, m, .normalLikely none)
      | (_, m) => let (c, m) := enterException c m EXC_TLBS (some vaddr); (c, m, .exception)
  | 0x1C =>  -- RRR: rz = rx op ry
    let rz := rx16 ((hw >>> 2) &&& 7)
    match hw &&& 3 with
    | 1 => let (c, m) := emitReg c m rz (c.r rx + c.r ry); (c, m, .normalLikely none)
    | 3 => let (c, m) := emitReg c m rz (c.r rx - c.r ry); (c, m, .normalLikely none)
    | _ => ({ c with halted := true }, m.emit (.unsupported pc (hw &&& 3) "mips16_rrr"), .halt)
  | 0x1D =>  -- RR: two-operand operations
    let rrFunct := hw &&& 0x1f
    match rrFunct with
    | 0x00 =>  -- JR/JRC/JALRC variants (distinguished by bits[7:5]=ry3)
      match ry3 with
      | 0 =>  -- JR rx: jump with delay slot (bits[10:8]=rx3)
        (c, m, .normal (some (c.r rx)))
      | 1 =>  -- JR $ra: jump with delay slot
        (c, m, .normal (some (c.r 31)))
      | 4 =>  -- JRC rx: jump, no delay slot, preserve bit0 for mode
        (c, m, .normalLikely (some (c.r rx)))
      | 5 =>  -- JRC $ra: jump $ra, no delay slot
        (c, m, .normalLikely (some (c.r 31)))
      | 6 =>  -- JALRC rx: $ra = (physPc+2)|1, jump to rx, no delay slot
        let rawTarget := c.r rx
        let linkAddr := (physPc + 2) ||| 1
        let (c, m) := emitReg c m 31 linkAddr
        (c, m, .normalLikely (some rawTarget))
      | _ => ({ c with halted := true }, m.emit (.unsupported pc ry3 "mips16_jr_sub"), .halt)
    | 0x01 => ({ c with halted := true }, m.emit (.note "mips16_sdbbp"), .halt)
    | 0x02 =>  -- SLT: T = (rx < ry) ? 1 : 0 (signed)
      let (c, m) := emitReg c m tReg16 (BitVec.ofNat 32 (if BitVec.slt (c.r rx) (c.r ry) then 1 else 0))
      (c, m, .normalLikely none)
    | 0x03 =>  -- SLTU: T = (rx < ry) ? 1 : 0 (unsigned)
      let (c, m) := emitReg c m tReg16 (BitVec.ofNat 32 (if (c.r rx).toNat < (c.r ry).toNat then 1 else 0))
      (c, m, .normalLikely none)
    | 0x04 =>  -- SLLV: ry <<= rx (rx is shift amount)
      let sh := (c.r rx).toNat &&& 31
      let (c, m) := emitReg c m ry (c.r ry <<< sh); (c, m, .normalLikely none)
    | 0x05 => ({ c with halted := true }, m.emit (.note "mips16_break"), .halt)
    | 0x06 =>  -- SRLV: ry >>>= rx (logical)
      let sh := (c.r rx).toNat &&& 31
      let (c, m) := emitReg c m ry (c.r ry >>> sh); (c, m, .normalLikely none)
    | 0x07 =>  -- SRAV: ry >>= rx (arithmetic)
      let sh := (c.r rx).toNat &&& 31
      let (c, m) := emitReg c m ry (BitVec.ofNat 32 (sar32 (c.r ry).toNat sh)); (c, m, .normalLikely none)
    | 0x0B =>  -- NEG: rx = -ry
      let (c, m) := emitReg c m rx (0 - c.r ry); (c, m, .normalLikely none)
    | 0x0C =>  -- AND: rx &= ry
      let (c, m) := emitReg c m rx (c.r rx &&& c.r ry); (c, m, .normalLikely none)
    | 0x0D =>  -- OR: rx |= ry
      let (c, m) := emitReg c m rx (c.r rx ||| c.r ry); (c, m, .normalLikely none)
    | 0x0E =>  -- XOR: rx ^= ry
      let (c, m) := emitReg c m rx (c.r rx ^^^ c.r ry); (c, m, .normalLikely none)
    | 0x0F =>  -- NOT: rx = ~ry
      let (c, m) := emitReg c m rx (~~~c.r ry); (c, m, .normalLikely none)
    | 0x10 =>  -- MFHI: rx = HI
      let (c, m) := emitReg c m rx c.hi; (c, m, .normalLikely none)
    | 0x12 =>  -- MFLO: rx = LO
      let (c, m) := emitReg c m rx c.lo; (c, m, .normalLikely none)
    | 0x18 =>  -- MULT: HI:LO = signed(rx)*signed(ry)
      let a := (c.r rx).toNat; let b := (c.r ry).toNat
      let sa := if a &&& 0x80000000 != 0 then 0xFFFFFFFF00000000 ||| a else a
      let sb := if b &&& 0x80000000 != 0 then 0xFFFFFFFF00000000 ||| b else b
      let res := (sa * sb) &&& 0xFFFFFFFFFFFFFFFF
      let c := { c with hi := BitVec.ofNat 32 (res >>> 32), lo := BitVec.ofNat 32 (res &&& 0xFFFFFFFF) }
      (c, m, .normalLikely none)
    | 0x19 =>  -- MULTU: HI:LO = unsigned(rx)*unsigned(ry)
      let res := (c.r rx).toNat * (c.r ry).toNat
      let c := { c with hi := BitVec.ofNat 32 (res >>> 32), lo := BitVec.ofNat 32 (res &&& 0xFFFFFFFF) }
      (c, m, .normalLikely none)
    | 0x1A =>  -- DIV: LO=T-quot, HI=T-rem (signed)
      let a := w2i (c.r rx); let b := w2i (c.r ry)
      if b == 0 then (c, m, .normalLikely none)
      else let c := { c with lo := i2w (tdiv a b), hi := i2w (tmod a b) }; (c, m, .normalLikely none)
    | 0x1B =>  -- DIVU: unsigned division
      let a := (c.r rx).toNat; let b := (c.r ry).toNat
      if b == 0 then (c, m, .normalLikely none)
      else let c := { c with lo := BitVec.ofNat 32 (a / b), hi := BitVec.ofNat 32 (a % b) }
           (c, m, .normalLikely none)
    | _ => ({ c with halted := true }, m.emit (.unsupported pc rrFunct "mips16_rr"), .halt)
  | _ => ({ c with halted := true }, m.emit (.unsupported pc op5 "mips16_op"), .halt)

-- Helper: compute next-PC increment based on the target mode bit
private def modeInc (target : Word) : Word :=
  if target.toNat &&& 1 == 0 then 4 else 2

-- MIPS16e step: c.pc has bit0=1 (ISA mode indicator); physical PC = c.pc & ~1.
-- Uses ISA-mode bit (bit0 of PC) to encode mode, not a separate field.
def step16 (c : Cpu) (m : Machine) : Cpu × Machine × Bool :=
  if c.halted then (c, m, false) else
  let pcFull := c.pc
  let physPc : Word := pcFull &&& (BitVec.ofNat 32 0xFFFFFFFE)
  let nextPc := c.npc
  let nextNpc := c.npc + modeInc c.npc
  let bump (m : Machine) : Machine := { m with icount := m.icount + 1 }
  match c.translate physPc with
  | none => let (c, m) := enterException c m EXC_TLBL (some physPc); (c, bump m, true)
  | some phys =>
    let (fres, m) := m.busRead phys 16 (fetch := true)
    match fres with
    | .error _ => ({ c with halted := true }, m.emit (.note "fetch16_fault"), false)
    | .ok hw16 =>
      let hw := hw16.toNat &&& 0xFFFF
      let op5 := (hw >>> 11) &&& 0x1f
      let m := m.emit (.exec pcFull (BitVec.ofNat 8 op5) "mips16")
      -- Handle 2-word JAL/JALX (op5=0x03) before EXTEND check
      if op5 == 0x03 then
        match c.translate (physPc + 2) with
        | none => let (c, m) := enterException c m EXC_TLBL (some (physPc + 2)); (c, bump m, true)
        | some phys2 =>
          let (hw2res, m) := m.busRead phys2 16 (fetch := true)
          match hw2res with
          | .error _ => ({ c with halted := true }, m.emit (.note "fetch16b_fault"), false)
          | .ok hw2_16 =>
            let hw2 := hw2_16.toNat &&& 0xFFFF
            let rBit := (hw >>> 10) &&& 1  -- 0=JAL(MIPS16e tgt), 1=JALX(MIPS32 tgt)
            -- Target: {PC[31:23], firstHw[9:5]<<18, hw2<<2}
            let top9 : Word := physPc &&& (BitVec.ofNat 32 0xFF800000)
            let mid : Word := BitVec.ofNat 32 (((hw &&& 0x3E0) >>> 5) <<< 18)
            let low : Word := BitVec.ofNat 32 (hw2 <<< 2)
            let tgtBase := top9 ||| mid ||| low
            -- JAL → target in MIPS16e (bit0=1); JALX → target in MIPS32 (bit0=0)
            let jumpTarget : Word := if rBit == 0 then tgtBase ||| 1 else tgtBase
            let linkAddr : Word := (physPc + 4) ||| 1  -- return in MIPS16e mode
            let (c, m) := emitReg c m 31 linkAddr
            -- JAL has delay slot at physPc+4 (= pcFull+4 since pcFull is odd)
            let dsAddr := pcFull + 4  -- delay slot in MIPS16e mode
            ({ c with pc := dsAddr, npc := jumpTarget }, bump m, true)
      -- Handle EXTEND prefix (op5=0x1E)
      else if op5 == 0x1E then
        let ext11 := hw &&& 0x7FF
        match c.translate (physPc + 2) with
        | none => let (c, m) := enterException c m EXC_TLBL (some (physPc + 2)); (c, bump m, true)
        | some phys2 =>
          let (bres, m) := m.busRead phys2 16 (fetch := true)
          match bres with
          | .error _ => ({ c with halted := true }, m.emit (.note "fetch16e_fault"), false)
          | .ok bw16 =>
            let bw := bw16.toNat &&& 0xFFFF
            -- Extended arithmetic immediate: sext((ext11<<5)|base[4:0], 16)
            let extImm16Raw := ((ext11 <<< 5) ||| (bw &&& 0x1f)) &&& 0xFFFF
            let extImm : Int := if extImm16Raw &&& 0x8000 != 0
              then Int.ofNat extImm16Raw - 0x10000 else Int.ofNat extImm16Raw
            -- Extended load/store byte offset: sext(ext11, 11)
            let extOff : Int := if ext11 &&& 0x400 != 0
              then Int.ofNat ext11 - 0x800 else Int.ofNat ext11
            let pc4 := pcFull + 4  -- address after the 4-byte EXTEND+base pair
            let npc4 := pc4 + modeInc pc4
            let (c, m, ctl) := execute16 c m pcFull bw extImm extOff true
            match ctl with
            | .exception => (c, bump m, true)
            | .halt => (c, bump m, false)
            | .eret => (c, bump m, true)
            | .normal branch =>
              let npc' := match branch with | some t => t | none => npc4
              ({ c with pc := pc4, npc := npc' }, bump m, true)
            | .normalLikely branch => match branch with
              | some tgt => ({ c with pc := tgt, npc := tgt + modeInc tgt }, bump m, true)
              | none => ({ c with pc := pc4, npc := npc4 }, bump m, true)
      else
        let (c, m, ctl) := execute16 c m pcFull hw 0 0 false
        match ctl with
        | .exception => (c, bump m, true)
        | .halt => (c, bump m, false)
        | .eret => (c, bump m, true)
        | .normal branch =>
          let npc' := match branch with | some t => t | none => nextNpc
          ({ c with pc := nextPc, npc := npc' }, bump m, true)
        | .normalLikely branch => match branch with
          | some tgt => ({ c with pc := tgt, npc := tgt + modeInc tgt }, bump m, true)
          | none => ({ c with pc := nextPc, npc := nextNpc }, bump m, true)

def step (c : Cpu) (m : Machine) : Cpu × Machine × Bool :=
  if c.halted then (c, m, false)
  else if c.pc.toNat &&& 1 == 1 then step16 c m  -- MIPS16e mode (bit0 of PC = 1)
  else
    let (c, m, fired) := timerAndIrq c m
    if fired then (c, { m with icount := m.icount + 1 }, true) else
    let pc := c.pc
    match c.translate pc with
    | none => let (c, m) := enterException c m EXC_TLBL (some pc); (c, { m with icount := m.icount + 1 }, true)
    | some phys =>
      let (fres, m) := m.busRead phys 32 (fetch := true)
      match fres with
      | .error _ => ({ c with halted := true }, m.emit (.note "fetch_fault"), false)
      | .ok word =>
        let w := word.toNat
        let op := (w >>> 26) &&& 0x3f
        let rs := (w >>> 21) &&& 0x1f
        let rt := (w >>> 16) &&& 0x1f
        let rd := (w >>> 11) &&& 0x1f
        let sa := (w >>> 6) &&& 0x1f
        let funct := w &&& 0x3f
        let imm := w &&& 0xffff
        let simm : Word := (BitVec.ofNat 16 imm).signExtend 32
        let m := m.emit (.exec pc (BitVec.ofNat 8 op) "mips")
        let nextPc := c.npc
        -- When c.npc targets MIPS16e (bit0=1), advance by 2; else by 4.
        let nextNpc := c.npc + modeInc c.npc
        let (c, m, ctl) := execute c m pc op rs rt rd sa funct imm simm
        let bump (m : Machine) : Machine := { m with icount := m.icount + 1 }
        match ctl with
        | .exception => (c, bump m, true)
        | .halt => (c, bump m, false)
        | .eret => (c, bump m, true)
        | .normal branch =>
          let npc' := match branch with | some t => t | none => nextNpc
          ({ c with pc := nextPc, npc := npc' }, bump m, true)
        | .normalLikely branch =>
          match branch with
          | some target => ({ c with pc := nextPc, npc := target }, bump m, true)
          | none => ({ c with pc := nextNpc, npc := nextNpc + modeInc nextNpc }, bump m, true)

def runMips (fuel : Nat) (s : St) : St :=
  Sei.Core.run (fun (s : St) =>
    let (c, m) := s
    if c.halted then (s, false)
    else let (c', m', cont) := step c m; ((c', m'), cont)) fuel s

/-! ### Assembler -/

def bvw (n : Nat) : Word := BitVec.ofNat 32 n
def iType (op rs rt imm : Nat) : Word := bvw ((op <<< 26) ||| (rs <<< 21) ||| (rt <<< 16) ||| (imm &&& 0xffff))
def rType (rs rt rd sa funct : Nat) : Word := bvw ((rs <<< 21) ||| (rt <<< 16) ||| (rd <<< 11) ||| (sa <<< 6) ||| funct)

def LUI (rt imm : Nat) : Word := iType 0x0F 0 rt imm
def ORI (rt rs imm : Nat) : Word := iType 0x0D rs rt imm
def ADDIU (rt rs imm : Nat) : Word := iType 0x09 rs rt imm
def LW (rt off base : Nat) : Word := iType 0x23 base rt off
def SW (rt off base : Nat) : Word := iType 0x2B base rt off
/-- BEQ rs,rt to absolute `target` from `cur`. -/
def BEQ (rs rt cur target : Nat) : Word :=
  iType 0x04 rs rt (((BitVec.ofNat 32 target - BitVec.ofNat 32 (cur + 4)) >>> 2).toNat &&& 0xffff)
def BNE (rs rt cur target : Nat) : Word :=
  iType 0x05 rs rt (((BitVec.ofNat 32 target - BitVec.ofNat 32 (cur + 4)) >>> 2).toNat &&& 0xffff)
def MFC0 (rt rd sel : Nat) : Word := bvw ((0x10 <<< 26) ||| (0x00 <<< 21) ||| (rt <<< 16) ||| (rd <<< 11) ||| sel)
def MTC0 (rt rd sel : Nat) : Word := bvw ((0x10 <<< 26) ||| (0x04 <<< 21) ||| (rt <<< 16) ||| (rd <<< 11) ||| sel)
def ERET : Word := bvw ((0x10 <<< 26) ||| (0x10 <<< 21) ||| 0x18)
def TLBWI : Word := bvw ((0x10 <<< 26) ||| (0x10 <<< 21) ||| 0x02)
def SYSCALL : Word := bvw 0x0C
def NOP : Word := bvw 0

def assemble (words : List Word) (little : Bool) : List Byte :=
  words.flatMap (fun w => encodeBytes little w.toNat 4)

end Sei.Isa.Mips
