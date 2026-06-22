/-
E22: raw P-code → SEI IR slice. A tiny raw-P-code subset (COPY, INT_ADD,
INT_SUB, LOAD, STORE, BRANCH, CBRANCH) over register/constant varnodes lowers to
`Sei.IR`, runs through the IR interpreter (emitting the typed `Effect` alphabet),
carries a source map (op index/byte → IR statement), and rejects an unsupported
op with a diagnostic. Needs `Sei.IR` (the lowering target).
-/
import Sei.Core
import Sei.Isa.Toy
import Sei.IR
open Sei.Core Sei.IR Sei.Isa.Toy
namespace Sei.Pcode

inductive VarNode
  | reg (i : Nat)
  | const (v : Nat)
  deriving Repr

inductive Op
  | copy    (dst src : VarNode)
  | intAdd  (dst a b : VarNode)
  | intSub  (dst a b : VarNode)
  | load    (dst addr : VarNode) (size : Nat)
  | store   (addr val : VarNode) (size : Nat)
  | branch  (target : Nat)
  | cbranch (cond : VarNode) (target : Nat)
  | unsupported (name : String)
  deriving Repr

def exprOf : VarNode → Expr
  | .reg i => .reg i
  | .const v => .const 32 v

def regOf : VarNode → Except String Nat
  | .reg i => .ok i
  | .const _ => .error "p-code: destination must be a register varnode"

/-- Lower one raw-P-code op to an IR statement (fails closed on unsupported ops). -/
def lowerOp : Op → Except String Stmt
  | .copy dst src    => do pure (.assign (.reg (← regOf dst)) (exprOf src))
  | .intAdd dst a b  => do pure (.assign (.reg (← regOf dst)) (.add (exprOf a) (exprOf b)))
  | .intSub dst a b  => do pure (.assign (.reg (← regOf dst)) (.sub (exprOf a) (exprOf b)))
  | .load dst addr size => do pure (.load (← regOf dst) (exprOf addr) (size * 8))
  | .store addr val size => pure (.store (exprOf addr) (exprOf val) (size * 8))
  | .branch t        => pure (.branch (.const 32 t))
  | .cbranch c t     => pure (.cbranch (.ne (exprOf c) (.const 32 0)) (.const 32 t))
  | .unsupported name => .error s!"unsupported p-code op: {name}"

def lowerPcode (ops : List Op) : Except String Block := ops.mapM lowerOp

/-- Source map: op index / byte offset → rendered IR statement. -/
def sourceMap (ops : List Op) : Except String (List (Nat × Nat × String)) :=
  ops.zipIdx.mapM fun (op, i) => do pure (i, i * 4, reprStr (← lowerOp op))

/-- Lower, type-check, and run a P-code block — only checked IR executes (finding 5). -/
def runPcode (ops : List Op) (m : Machine) : Except String Machine := do
  let block ← lowerPcode ops
  match TypedBlock.check block with
  | some tb => pure (execTyped tb ({ } : Cpu) m).2.1
  | none => .error "lowered p-code is ill-typed"

end Sei.Pcode
