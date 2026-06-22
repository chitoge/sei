/-
L3 (large-use-case plan): the frontier → device-hypothesis task. An unknown-MMIO
frontier in a run is turned into a candidate device task (address, access widths,
poll count, candidate fidelity class). A hypothesis device synthesized from it
(observational/derived) can then be attached to advance execution — recorded with
fidelity metadata, failing closed outside its window.
-/
import Sei.Core
namespace Sei.Hw
open Sei.Core

structure FrontierTask where
  address : Nat
  widths : List Nat
  pollCount : Nat
  candidateClass : SemClass
  deriving Repr, DecidableEq

/-- Extract unknown-MMIO frontiers from a trace, grouped by address. -/
def frontierTasks (m : Machine) : List FrontierTask := Id.run do
  let mut hits : List (Nat × Nat) := []          -- (address, width) per unknown read
  for ev in m.trace do
    match ev.effect with
    | .unknownRead a w _ => hits := hits ++ [(a.toNat, w)]
    | _ => pure ()
  return (hits.map (·.1)).eraseDups.map fun ad =>
    let evs := hits.filter (·.1 == ad)
    { address := ad, widths := (evs.map (·.2)).eraseDups, pollCount := evs.length,
      candidateClass := .derived }

/-- Synthesize a status-model device hypothesis for a polling frontier: returns 0
    for `readyAfter` reads then `readyValue` (the E04 pattern), classified derived. -/
def synthStatusDevice (t : FrontierTask) (readyAfter : Nat) (readyValue : Word) : Device :=
  { name := s!"synth_{t.address}", base := t.address, size := 4,
    beh := .statusModel 0 (some readyAfter) readyValue,
    sem := { id := s!"synth.{t.address}", cls := .derived, proofUse := .local,
             source := "synthesized from unknown-MMIO polling frontier",
             assumptions := ["polling loop advances once the status becomes ready"] } }

end Sei.Hw
