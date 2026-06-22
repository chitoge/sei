/-
Sei.IR test: the toy ISA lowered to IR executes identically to the direct
interpreter (same typed `Effect` log), every lowered block is well-typed, and a
deliberately ill-typed block is rejected by the checker. Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Toy
import Sei.IR
open Sei.Core Sei.Isa.Toy Sei.IR

def sumProg : List Word :=
  [MOVI 1 7, MOVI 2 0, MOVI 3 0x1000, ADD 2 2 1, ADDI 1 1 0xffff,
   BNZ 1 0xfffe, STR 2 3 0, HALT]

def machine : Cpu × Machine :=
  let rom := mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") true (bytesToBA (assemble sumProg true))
  let ram := mkRegion "ram" 0x1000 0x1000 Kind.ram (parsePerms "rw") true
  (({} : Cpu), { regions := #[rom, ram], unknownDefault := 0 })

def directTrace : Array Event := (runToy 200 machine).2.trace
def irTrace : Array Event := (runToyIR 200 machine).2.trace

/-- Every instruction in the program lowers to a well-typed IR block. -/
def allLoweredWellTyped : Bool :=
  sumProg.all fun w =>
    let n := w.toNat
    (lowerToy 0 ((n >>> 24) &&& 0xff) ((n >>> 20) &&& 0xf) ((n >>> 16) &&& 0xf) (n &&& 0xffff)).wellTyped

/-- An ill-typed block: a 16-bit value assigned to a 32-bit register. -/
def badBlock : Block := [.assign (.reg 0) (.const 16 5)]

def checks : List (String × Bool) :=
  [ ("direct_ir_equiv", decide (directTrace = irTrace)),
    ("nonempty_trace", decide (irTrace.size > 0)),
    ("lowered_well_typed", allLoweredWellTyped),
    ("bad_block_rejected", badBlock.wellTyped == false),
    -- finding 5: an ill-typed block cannot be wrapped, so it can't reach execTyped
    ("typed_check_rejects_bad", (TypedBlock.check badBlock).isNone),
    ("typed_check_accepts_good", (TypedBlock.check (lowerToy 0 0x01 1 0 7)).isSome) ]

def main : IO Unit := do
  IO.println s!"direct={directTrace.size} ir={irTrace.size} events"
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "IR equivalence/typecheck failed")
  IO.println "IR: PASS"
