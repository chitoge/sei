/-
Sei.IR (audit B2): a small typed effect IR — the common lowering target a Sail/
SLEIGH importer would eventually produce. v0 is enough to lower the toy ISA:
typed BitVec expressions, register/memory lvalues, statements (assign, load,
store, branch, cbranch, trap), a width type-checker, and an interpreter that
emits the SAME typed `Effect` alphabet as the direct ISA interpreters — so direct
and IR execution produce identical event logs.
-/
import Sei.Core
import Sei.Isa.Toy
open Sei.Core Sei.Isa.Toy

namespace Sei.IR

/-! ### Types -/

inductive Ty
  | bv (w : Nat)
  | bool
  deriving DecidableEq, Repr

/-! ### Expressions (registers are 32-bit `Word`s) -/

inductive Expr
  | const (w v : Nat)
  | reg   (i : Nat)
  | add   (a b : Expr)
  | sub   (a b : Expr)
  | ne    (a b : Expr)         -- bool
  | sext  (fromW toW : Nat) (e : Expr)
  deriving Repr

inductive LVal
  | reg (i : Nat)
  deriving Repr

inductive Stmt
  | assign  (lv : LVal) (e : Expr)
  | load    (dst : Nat) (addr : Expr) (width : Nat)
  | store   (addr val : Expr) (width : Nat)
  | branch  (target : Expr)
  | cbranch (cond target : Expr)
  | trap    (kind : String)
  deriving Repr

abbrev Block := List Stmt

/-! ### Type checker (width consistency) -/

def Expr.tyOk : Expr → Option Ty
  | .const w _ => some (.bv w)
  | .reg _ => some (.bv 32)
  | .add a b | .sub a b =>
    match a.tyOk, b.tyOk with
    | some (.bv x), some (.bv y) => if x == y then some (.bv x) else none
    | _, _ => none
  | .ne a b =>
    match a.tyOk, b.tyOk with
    | some (.bv x), some (.bv y) => if x == y then some .bool else none
    | _, _ => none
  | .sext fromW toW e =>
    match e.tyOk with
    | some (.bv w) => if w == fromW || w == 32 then some (.bv toW) else none
    | _ => none

def validWidth (w : Nat) : Bool := w == 8 || w == 16 || w == 32

def stmtOk : Stmt → Bool
  | .assign (.reg _) e => e.tyOk == some (.bv 32)
  | .load _ addr w => addr.tyOk == some (.bv 32) && validWidth w
  | .store addr val w => addr.tyOk == some (.bv 32) && val.tyOk == some (.bv 32) && validWidth w
  | .branch t => t.tyOk == some (.bv 32)
  | .cbranch c t => c.tyOk == some Ty.bool && t.tyOk == some (.bv 32)
  | .trap _ => true

def Block.wellTyped (b : Block) : Bool := b.all stmtOk

/-- A block proven well-typed — the only thing the public execution API accepts
    (finding 5: enforce the typechecker by construction, not by convention). -/
structure TypedBlock where
  block : Block
  ok : block.wellTyped = true

/-- The only way to build a `TypedBlock`: ill-typed blocks return `none`, so they
    can never reach `execTyped`. -/
def TypedBlock.check (b : Block) : Option TypedBlock :=
  if h : b.wellTyped = true then some ⟨b, h⟩ else none

/-! ### Interpreter (emits the same `Effect` alphabet) -/

def evalExpr (r : Nat → Word) : Expr → Word
  | .const w v => BitVec.ofNat 32 (v % (2 ^ w))
  | .reg i => r i
  | .add a b => evalExpr r a + evalExpr r b
  | .sub a b => evalExpr r a - evalExpr r b
  | .ne a b => if evalExpr r a == evalExpr r b then 0 else 1
  | .sext fromW _ e => (BitVec.ofNat fromW (evalExpr r e).toNat).signExtend 32

/-- Execute one statement; threads a pending branch target and a halt flag. -/
def execStmt (s : Stmt) (c : Cpu) (m : Machine) (br : Option Word)
    : Cpu × Machine × Option Word × Bool :=
  match s with
  | .assign (.reg i) e =>
    let v := evalExpr c.r e
    (c.setR i v, m.emit (.reg i v), br, false)
  | .load dst addr w =>
    let a := evalExpr c.r addr
    let (res, m) := m.busRead a w
    match res with
    | .ok v => (c.setR dst v, m.emit (.reg dst v), br, false)
    | .error _ => (c, m.emit (.note "data_abort"), br, true)
  | .store addr val w =>
    let (res, m) := m.busWrite (evalExpr c.r addr) (evalExpr c.r val) w
    match res with
    | .ok _ => (c, m, br, false)
    | .error _ => (c, m.emit (.note "data_abort"), br, true)   -- fault halts the block
  | .branch t => (c, m, some (evalExpr c.r t), false)
  | .cbranch cond t =>
    if evalExpr c.r cond != 0 then (c, m, some (evalExpr c.r t), false) else (c, m, br, false)
  | .trap _ => (c, m, br, true)

/-- Raw block execution — internal; callers should use `execTyped`. -/
def execBlock (b : Block) (c0 : Cpu) (m0 : Machine) : Cpu × Machine × Option Word × Bool :=
  b.foldl (fun st s =>
    let (c, m, br, h) := st
    if h then st else execStmt s c m br) (c0, m0, none, false)

/-- Public IR execution API: accepts only type-checked blocks (finding 5). -/
def execTyped (tb : TypedBlock) (c0 : Cpu) (m0 : Machine) : Cpu × Machine × Option Word × Bool :=
  execBlock tb.block c0 m0

/-! ### Toy ISA → IR -/

def lowerToy (pc : Word) (op rd rs imm : Nat) : Block :=
  let rt := imm &&& 0xf
  let simmTarget : Word := pc + (BitVec.ofNat 16 imm).signExtend 32 * 4
  match op with
  | 0x00 => [.trap "halt"]
  | 0x01 => [.assign (.reg rd) (.const 32 imm)]
  | 0x02 => [.assign (.reg rd) (.add (.reg rs) (.reg rt))]
  | 0x03 => [.assign (.reg rd) (.sub (.reg rs) (.reg rt))]
  | 0x04 => [.assign (.reg rd) (.add (.reg rs) (.sext 16 32 (.const 16 imm)))]
  | 0x05 => [.load rd (.add (.reg rs) (.sext 16 32 (.const 16 imm))) 32]
  | 0x06 => [.store (.add (.reg rs) (.sext 16 32 (.const 16 imm))) (.reg rd) 32]
  | 0x07 => [.cbranch (.ne (.reg rs) (.const 32 0)) (.const 32 simmTarget.toNat)]
  | 0x08 => [.branch (.const 32 simmTarget.toNat)]
  | 0x09 => [.load rd (.add (.reg rs) (.sext 16 32 (.const 16 imm))) 8]
  | _ => [.trap "undef"]

/-- IR-based toy step: fetch + exec exactly as the direct interpreter, then run
    the lowered IR block. -/
def stepIR (c : Cpu) (m : Machine) : Cpu × Machine × Bool :=
  if c.halted then (c, m, false)
  else
    let pc := c.pc
    let (fres, m) := m.busRead pc 32 (fetch := true)
    match fres with
    | .error _ => ({ c with halted := true }, m.emit (.note "fetch_fault"), false)
    | .ok word =>
      let w := word.toNat
      let op := (w >>> 24) &&& 0xff
      let rd := (w >>> 20) &&& 0xf
      let rs := (w >>> 16) &&& 0xf
      let imm := w &&& 0xffff
      let m := m.emit (.exec pc (BitVec.ofNat 8 op) (mnem op))
      let nextpc : Word := pc + 4
      -- lower → type-check → execute only the checked block (finding 5)
      let (c, m, br, halted) := match TypedBlock.check (lowerToy pc op rd rs imm) with
        | some tb => execTyped tb c m
        | none => (c, m.emit (.note "ill_typed_block"), none, true)
      ({ c with pc := br.getD nextpc, halted := halted },
       { m with icount := m.icount + 1 }, ¬ halted)

def runToyIR (fuel : Nat) (s : Cpu × Machine) : Cpu × Machine :=
  Sei.Core.run (fun (s : Cpu × Machine) =>
    let (c, m) := s
    if c.halted then (s, false)
    else let (c', m', cont) := stepIR c m; ((c', m'), cont)) fuel s

/-! ### Type-checker proofs -/

/-- An ill-typed block (a 16-bit value into a 32-bit register) is rejected. -/
theorem badBlock_rejected :
    Block.wellTyped [Stmt.assign (LVal.reg 0) (Expr.const 16 5)] = false := by decide

/-- A lowered toy ADD is well-typed. -/
theorem add_lowering_wellTyped : (lowerToy 0 0x02 2 2 1).wellTyped = true := by decide

/-- A lowered toy ADDI (with the sign-extended immediate) is well-typed. -/
theorem addi_lowering_wellTyped : (lowerToy 0 0x04 1 1 0xffff).wellTyped = true := by decide

end Sei.IR
