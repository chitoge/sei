/-
Fidelity substrate test (E13 event classification + E14 enforcement): every
event carries its producing unit's declared class/id; the no-gloss combination
rules are enforced; and a real run keeps the whole-trace anti-gloss guarantee.
Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Toy
import Sei.Fidelity
open Sei.Core Sei.Isa.Toy

def sumProg : List Word :=
  [MOVI 1 7, MOVI 2 0, MOVI 3 0x1000, ADD 2 2 1, ADDI 1 1 0xffff,
   BNZ 1 0xfffe, STR 2 3 0, HALT]

def toyMachine : Cpu × Machine :=
  let rom := mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") true (bytesToBA (assemble sumProg true))
  let ram := mkRegion "ram" 0x1000 0x1000 Kind.ram (parsePerms "rw") true
  (({} : Cpu), { regions := #[rom, ram], unknownDefault := 0 })

-- Devices with DECLARED fidelity (not inferred from `beh`).
def uartDev : Device :=
  { name := "uart0", base := 0x9000, size := 0x100, beh := .uart [] [] 1 0,
    sem := { id := "uart0", cls := .spec, proofUse := .local, source := "hand-authored" } }
def statusDev : Device :=
  { name := "st", base := 0x8000, size := 4, beh := .statusModel 0 (some 3) 1,
    sem := { id := "e04.status", cls := .derived, proofUse := .local, source := "E04 synthesis" } }

def devMachine : Machine :=
  { regions := #[mkRegion "ram" 0 0x1000 Kind.ram (parsePerms "rw") true],
    devices := #[uartDev, statusDev] }

def lastEvent (m : Machine) : Option Event := m.trace.back?

def eventClassAt (addr : Nat) (wantCls : SemClass) (wantId : Option String) : Bool :=
  match lastEvent (devMachine.busRead (BitVec.ofNat 32 addr) 32).2 with
  | some ev => ev.prov.cls == wantCls && (wantId.isNone || ev.prov.semId == wantId)
  | none => false

def checks : List (String × Bool) :=
  [ -- E13: events carry the producing unit's declared class + id
    ("uart_event_spec", eventClassAt 0x9004 .spec (some "uart0")),
    ("status_event_derived", eventClassAt 0x8000 .derived (some "e04.status")),
    ("unknown_event_unknown", eventClassAt 0xF000 .unknown none),
    -- anti-gloss over a real run
    ("toy_run_all_meta_ok", (runToy 200 toyMachine).2.allMetaOk),
    ("dev_run_all_meta_ok", (devMachine.busRead 0xF000 32).2.allMetaOk),
    -- E14: no-gloss enforcement
    ("enforce_spec_full_ok", validCombo .spec .full),
    ("enforce_unknown_full_rejected", validCombo .unknown .full == false),
    ("enforce_observational_full_rejected", validCombo .observational .full == false),
    ("enforce_derived_full_rejected", validCombo .derived .full == false),
    ("enforce_derived_local_ok", validCombo .derived .local),
    ("enforce_unknown_none_ok", validCombo .unknown .none) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "fidelity checks failed")
  IO.println "fidelity: PASS"
