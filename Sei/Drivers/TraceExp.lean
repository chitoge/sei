/-
E23 test: a captured MMIO polling trace becomes a `traceReplay` device. It
replays the captured responses in order, is deterministic across runs (pure
value model ⇒ snapshot/replay is definitional), fails closed outside the captured
envelope (returns the explicit `traceFrontier` sentinel, never a fabricated
value), and is classified `traceReplay` / `proof_use: none`. Exit 0 = pass.
-/
import Sei.Core
open Sei.Core

-- Captured polling: STATUS@0x0 reads 0,0,0,1 (becomes ready), then DR@0x4 reads 0x42.
def script : List (Nat × Word) := [(0x0, 0), (0x0, 0), (0x0, 0), (0x0, 1), (0x4, 0x42)]

def DEVBASE : Nat := 0x50000000

def dev : Device :=
  { name := "captured0", base := DEVBASE, size := 0x100, beh := .traceReplay script 0,
    sem := { id := "captured0", cls := .traceReplay, proofUse := .none, source := "HIL capture" } }

def machine : Machine :=
  { regions := #[mkRegion "ram" 0 0x1000 Kind.ram (parsePerms "rw") true], devices := #[dev] }

def replay (m : Machine) (offs : List Nat) : List Word := Id.run do
  let mut m := m
  let mut outs : List Word := []
  for off in offs do
    let (r, m') := m.busRead (BitVec.ofNat 32 (DEVBASE + off)) 32
    m := m'
    outs := outs ++ [r.toOption.getD 0]
  return outs

def inEnvelope : List Nat := [0x0, 0x0, 0x0, 0x0, 0x4]

def outOfEnvelope : Bool :=
  -- first read is offset 0x4 but the next scripted response is for 0x0 → fail closed
  ((machine.busRead (BitVec.ofNat 32 (DEVBASE + 0x4)) 32).1.toOption.getD 0) == traceFrontier

def checks : List (String × Bool) :=
  [ ("replays_captured_values", replay machine inEnvelope == [0, 0, 0, 1, 0x42]),
    ("deterministic", replay machine inEnvelope == replay machine inEnvelope),
    ("fails_closed_out_of_envelope", outOfEnvelope),
    ("class_is_traceReplay", dev.sem.cls == SemClass.traceReplay),
    ("proof_use_none", dev.sem.proofUse == ProofUse.none) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "trace-replay checks failed")
  IO.println "trace replay (E23): PASS"
