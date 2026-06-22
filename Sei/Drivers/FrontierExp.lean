/-
L3 test: frontier-driven device synthesis. A toy firmware polls an unknown MMIO
status until ready, then writes a marker. With no device it loops at the frontier
(no marker). The frontier is extracted as a task; a synthesized status device
(derived) is attached, and the same firmware now advances past the poll and writes
the marker. Out-of-window access still fails closed. Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Toy
import Sei.Hw.Frontier
open Sei.Core Sei.Isa.Toy Sei.Hw

-- poll [0x8000] until nonzero, then store 0x42 at 0x1000
def pollProg : List Word :=
  [ MOVI 3 0x8000, MOVI 4 0x42, MOVI 5 0x1000,
    LDR 1 3 0,        -- 0x0C: poll status
    BNZ 1 2,          -- 0x10: if ready, jump to STR (0x18)
    B 0xfffe,         -- 0x14: else loop back to 0x0C
    STR 4 5 0,        -- 0x18: write marker
    HALT ]

def baseM : Machine :=
  { regions := #[mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") true (bytesToBA (assemble pollProg true)),
                 mkRegion "ram" 0x1000 0x1000 Kind.ram (parsePerms "rw") true] }

def st (devs : Array Device) : Cpu × Machine := (({} : Cpu), { baseM with devices := devs })

def hasMarker (m : Machine) : Bool :=
  m.effects.any fun e => match e with | .memWrite a _ v => a == (0x1000 : Word) && v == (0x42 : Word) | _ => false

def beforeM : Machine := (runToy 300 (st #[])).2
def tasks : List FrontierTask := frontierTasks beforeM
def synth : Option Device := match tasks with | t :: _ => some (synthStatusDevice t 3 1) | [] => none
def afterM : Machine := match synth with | some d => (runToy 300 (st #[d])).2 | none => beforeM

-- a read outside the synthesized device window is still an unknown frontier
def outOfEnvelope : Bool :=
  match synth with
  | some d =>
    let m : Machine := { baseM with devices := #[d] }
    (m.busRead 0x9000 32).2.effects.any fun e => match e with
      | .unknownRead a _ _ => a == (0x9000 : Word) | _ => false
  | none => false

def checks : List (String × Bool) :=
  [ ("frontier_detected", match tasks with | t :: _ => t.address == 0x8000 | [] => false),
    ("poll_count_positive", match tasks with | t :: _ => t.pollCount > 0 | [] => false),
    ("before_no_progress", ! hasMarker beforeM),
    ("after_advances_past_frontier", hasMarker afterM),
    ("hypothesis_is_derived", match synth with | some d => d.sem.cls == SemClass.derived | none => false),
    ("out_of_envelope_fails_closed", outOfEnvelope) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "frontier synthesis checks failed")
  IO.println "frontier-driven device synthesis (L3): PASS"
