/-
E09 (pure Lean, no Python): differential equivalence between two independent toy
backends —
  * the executable core-backed ISA (`Sei.Isa.Toy.runToy` over `Machine`/`busRead`/
    typed `Effect`), and
  * an independent Nat-based flat-state backend (`Sei.Isa.ToyAlt`).
Both render the same canonical event log; the test asserts they are identical.
Exit 0 = equivalent. (Replaces the former Python "native" oracle + golden file.)
-/
import Sei.Core
import Sei.Isa.Toy
import Sei.Isa.ToyAlt
open Sei.Core
open Sei.Isa.Toy

def hexNo (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- Render the core's typed effects to the canonical F/X/R/W lines. -/
def canon : Effect → Option String
  | .fetch a w      => some s!"F {hexNo a.toNat} {hexNo w.toNat}"
  | .exec _ op _    => some s!"X {hexNo op.toNat}"
  | .reg i v        => some s!"R {i} {hexNo v.toNat}"
  | .memWrite a _ v => some s!"W {hexNo a.toNat} {hexNo v.toNat}"
  | _ => none

def sumProg : List Word :=
  [MOVI 1 7, MOVI 2 0, MOVI 3 0x1000, ADD 2 2 1, ADDI 1 1 0xffff,
   BNZ 1 0xfffe, STR 2 3 0, HALT]

def machine : St :=
  let rom := mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") true (bytesToBA (assemble sumProg true))
  let ram := mkRegion "ram" 0x1000 0x1000 Kind.ram (parsePerms "rw") true
  (({} : Cpu), { regions := #[rom, ram], unknownDefault := 0 })

def coreLines : List String :=
  let (_, m) := runToy 1000 machine
  m.effects.toList.filterMap canon

/-- First index where two lists differ (for a readable failure message). -/
def firstDiff : List String → List String → Option (Nat × String × String)
  | [], [] => none
  | a :: as, b :: bs => if a == b then (firstDiff as bs).map (fun (i, x, y) => (i+1, x, y))
                        else some (0, a, b)
  | a :: _, [] => some (0, a, "<eof>")
  | [], b :: _ => some (0, "<eof>", b)

def main : IO Unit := do
  let a := coreLines
  let b := Sei.Isa.ToyAlt.canonLines
  if a == b then
    IO.println s!"EQUIVALENT: core-backed toy == independent Lean backend ({a.length} events)"
  else
    match firstDiff a b with
    | some (i, x, y) => IO.println s!"MISMATCH at {i}: core={x} alt={y}"
    | none => IO.println "MISMATCH (length)"
    throw (IO.userError "toy equivalence failed")
