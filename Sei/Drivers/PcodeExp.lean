/-
E22 test: lower a tiny raw-P-code program to SEI IR, run it through the IR
interpreter, and confirm the typed effects (register writes + a memory store);
the source map maps each op to its IR statement; an unsupported op is rejected
with a diagnostic. Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Toy
import Sei.IR
import Sei.Hw.Pcode
open Sei.Core Sei.Pcode

/-- r1=7 ; r2=0x1000 ; r3=r1+5 ; store32 [r2]=r3 -/
def prog : List Op :=
  [ .copy (.reg 1) (.const 7),
    .copy (.reg 2) (.const 0x1000),
    .intAdd (.reg 3) (.reg 1) (.const 5),
    .store (.reg 2) (.reg 3) 4 ]

def machine : Machine :=
  { regions := #[mkRegion "ram" 0x1000 0x1000 Kind.ram (parsePerms "rw") true] }

def isErr {α} : Except String α → Bool | .error _ => true | .ok _ => false

def pcodeChecks : Except String (List (String × Bool)) := do
  let m ← runPcode prog machine
  let regWrote := fun (i : Nat) (v : Word) => m.effects.any fun e => match e with
    | .reg j w => j == i && w == v | _ => false
  let stored := m.effects.any fun e => match e with
    | .memWrite a _ v => a == (0x1000 : Word) && v == (12 : Word) | _ => false
  let sm ← sourceMap prog
  pure [ ("r1_eq_7", regWrote 1 7),
         ("r3_eq_12", regWrote 3 12),
         ("store_r3_at_0x1000", stored),
         ("source_map_complete", sm.length == prog.length),
         ("unsupported_op_rejected", isErr (lowerPcode [Op.unsupported "FLOAT_ADD"])) ]

def main : IO Unit := do
  match pcodeChecks with
  | .error e => throw (IO.userError s!"p-code lowering failed: {e}")
  | .ok checks =>
    let mut ok := true
    for (n, b) in checks do
      let tag := if b then "ok" else "FAIL"
      IO.println s!"{n}: {tag}"
      if !b then ok := false
    if !ok then throw (IO.userError "p-code checks failed")
    IO.println "p-code → IR (E22): PASS"
