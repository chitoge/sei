/-
Audit (memory-provider / true gated memory): a DDR controller gates a real DRAM
*region*, not just a register. The DRAM region is off the bus (disabled) until the
firmware runs the init sequence (write 1 to CTRL); before that, a DRAM access
fails; after, the same address resolves to the fast memory substrate. Ordinary
RAM stays always-on. Snapshot/restore is the pure Machine value. Exit 0 = pass.
-/
import Sei.Core
open Sei.Core

def DDR_CTRL : Nat := 0x70000000
def DRAM : Nat := 0x80000000

-- DRAM region holding 0xD4A at offset 0, GATED off the bus until the controller is ready.
def dramRegion : Region :=
  { mkRegion "dram" DRAM 0x1000 Kind.ram (parsePerms "rw") true (bytesToBA (encodeBytes true 0xD4A 4))
    with enabled := false }

def ddrCtrl : Device :=
  { name := "ddr0", base := DDR_CTRL, size := 0x100, beh := .ddr false "dram",
    sem := { id := "ddr0", cls := .observational, proofUse := .none,
             source := "DDR controller (gates the dram region until init)" } }

def machine : Machine :=
  { regions := #[mkRegion "ram" 0 0x1000 Kind.ram (parsePerms "rw") true, dramRegion],
    devices := #[ddrCtrl], unknownRead := .fault }   -- strict: ungated DRAM access faults

def dramBefore : Except Fault Word := (machine.busRead (BitVec.ofNat 32 DRAM) 32).1
def afterInit : Machine := (machine.busWrite (BitVec.ofNat 32 (DDR_CTRL + 0x4)) 1 32).2
def statusReady : Word := (afterInit.busRead (BitVec.ofNat 32 DDR_CTRL) 32).1.toOption.getD 0
def dramAfter : Word := (afterInit.busRead (BitVec.ofNat 32 DRAM) 32).1.toOption.getD 0
def ramAlwaysOn : Bool := match (machine.busRead (BitVec.ofNat 32 0) 32).1 with | .ok _ => true | _ => false

def checks : List (String × Bool) :=
  [ ("dram_faults_before_init", match dramBefore with | .error _ => true | _ => false),
    ("ram_always_on_fast_path", ramAlwaysOn),
    ("status_ready_after_init", statusReady == 1),
    ("dram_accessible_after_init", dramAfter == 0xD4A),
    ("class_observational", ddrCtrl.sem.cls == SemClass.observational) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "DDR memory-provider checks failed")
  IO.println "DDR memory-provider readiness gate: PASS"
