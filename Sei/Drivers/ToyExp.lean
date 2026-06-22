/-
Toy-ISA experiments in Lean (no Python): basic execution, E04 (unknown-MMIO
frontier loop + device hypothesis), and E08 (determinism + fork). Exit 0 = pass.

Note how the FM-friendly pure design makes E08 almost trivial: `runToy` is a pure
function, so determinism is definitional and a "snapshot" is just a value — fork
independence needs no copying.
-/
import Sei.Core
import Sei.Isa.Toy
open Sei.Core
open Sei.Isa.Toy

def little : Bool := true

def romImage (prog : List Word) : Region :=
  mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") little (bytesToBA (assemble prog little))
def ram : Region := mkRegion "ram" 0x1000 0x1000 Kind.ram (parsePerms "rw") little

def machineOf (prog : List Word) (devs : Array Device := #[]) : St :=
  (({} : Cpu), { regions := #[romImage prog, ram], devices := devs, unknownDefault := 0 })

-- SUM: r2 := 7+6+...+1 = 28, stored at 0x1000.
def sumProg : List Word :=
  [MOVI 1 7, MOVI 2 0, MOVI 3 0x1000, ADD 2 2 1, ADDI 1 1 0xffff,
   BNZ 1 0xfffe, STR 2 3 0, HALT]

-- POLL: spin on unknown status @0x8000 until non-zero, then write marker 0xAB.
def pollProg : List Word :=
  [MOVI 5 0x8000, MOVI 6 0x1000, LDR 1 5 0, BNZ 1 0x0002, B 0xfffe,
   MOVI 2 0xAB, STR 2 6 0, HALT]

def hasMarker (m : Machine) : Bool :=
  m.effects.any (fun e => match e with
    | .memWrite a _ v => a == (0x1000 : Word) && v == (0xAB : Word) | _ => false)

def countUnknown (m : Machine) : Nat :=
  (m.effects.filter (·.isUnknownMmio)).size

def statusDev (readyAfter : Option Nat) : Device :=
  { name := "status", base := 0x8000, size := 4, beh := .statusModel 0 readyAfter 1,
    sem := { id := "e04.status", cls := .derived, proofUse := .local,
             source := "E04 unknown-MMIO synthesis" } }

def checks : List (String × Bool) := Id.run do
  let mut cs : List (String × Bool) := []

  -- 1. basic execution
  let (c, _) := runToy 200 (machineOf sumProg)
  cs := cs ++ [("sum_r2_eq_28", c.r 2 == (28 : Word))]

  -- 2. E04 blocked: no device → unknown-MMIO frontier, marker never written
  let (cB, mB) := runToy 80 (machineOf pollProg)
  cs := cs ++ [("e04_unknown_traced", decide (countUnknown mB ≥ 3)),
               ("e04_blocked_no_marker", (! hasMarker mB) && (! cB.halted))]

  -- 3. E04 advanced: attach a status model that goes ready after 3 reads
  let (cA, mA) := runToy 80 (machineOf pollProg #[statusDev (some 3)])
  cs := cs ++ [("e04_advanced_marker", hasMarker mA && cA.halted)]

  -- 4. E08 determinism: two pure runs are identical
  let (_, m1) := runToy 200 (machineOf sumProg)
  let (_, m2) := runToy 200 (machineOf sumProg)
  cs := cs ++ [("e08_deterministic", decide (m1.trace = m2.trace))]

  -- 5. E08 fork: one snapshot (a value), two device hypotheses, isolated outcomes
  let snap : St := machineOf pollProg            -- the pre-run snapshot value
  let (fa, ma) := runToy 80 (snap.1, { snap.2 with devices := #[statusDev (some 2)] })
  let (fb, mb) := runToy 80 (snap.1, { snap.2 with devices := #[statusDev none] })
  cs := cs ++ [("e08_fork_diverges", (hasMarker ma && fa.halted) && (! hasMarker mb)),
               ("e08_snapshot_untouched", decide (snap.2.devices.size = 0))]

  return cs

def main : IO Unit := do
  let mut allOk := true
  for (name, ok) in checks do
    let st := if ok then "ok" else "FAIL"
    IO.println s!"{name}: {st}"
    if !ok then allOk := false
  if !allOk then throw (IO.userError "toy experiments failed")
  IO.println "toy experiments: PASS"
