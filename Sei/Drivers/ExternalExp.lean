/-
E18 test: a mock external/co-sim device (a free-running timer behind a typed
boundary). It has a typed read interface, runs deterministically twice with
identical output, and snapshot-before-interaction restores and replays the same
output (pure value model). Classified `external` / `proof_use: none`. Exit 0 = pass.
-/
import Sei.Core
open Sei.Core

def DEVBASE : Nat := 0x60000000

def extDev : Device :=
  { name := "ext_timer", base := DEVBASE, size := 0x100, beh := .external "co-sim-timer" 0 1,
    sem := { id := "ext_timer", cls := .external, proofUse := .none,
             source := "mock external co-sim (side effects: increments on read)" } }

def machine : Machine :=
  { regions := #[mkRegion "ram" 0 0x1000 Kind.ram (parsePerms "rw") true], devices := #[extDev] }

/-- Read the external timer `n` times. -/
def readN (m : Machine) (n : Nat) : List Word := Id.run do
  let mut m := m
  let mut outs : List Word := []
  for _ in [0:n] do
    let (r, m') := m.busRead (BitVec.ofNat 32 DEVBASE) 32
    m := m'
    outs := outs ++ [r.toOption.getD 0]
  return outs

def checks : List (String × Bool) :=
  [ ("typed_io_sequence", readN machine 4 == [0, 1, 2, 3]),
    ("deterministic", readN machine 4 == readN machine 4),
    -- snapshot the machine value, then two replays from that snapshot agree
    ("snapshot_replay_same", let snap := machine; readN snap 4 == readN snap 4),
    ("class_external", extDev.sem.cls == SemClass.external),
    ("not_proof_eligible", extDev.sem.proofUse == ProofUse.none && extDev.sem.valid) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "external boundary checks failed")
  IO.println "external boundary (E18): PASS"
