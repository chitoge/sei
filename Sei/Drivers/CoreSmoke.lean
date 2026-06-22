/- Smoke + N0 negative tests: validates the Lean Core substrate (typed BitVec
   memory, endian, bus, unknown-MMIO frontier) and the audit fixes — cross-region
   bounds faults (A1), unknown-MMIO fault policy (A2), and non-overlap decode
   well-formedness (A3). Exit 0 = all checks pass. -/
import Sei.Core
open Sei.Core

def build (little : Bool) : Machine :=
  { regions := #[
      mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") little
        (bytesToBA [0x00, 0x11, 0x22, 0x33]),
      mkRegion "ram" 0x1000 0x1000 Kind.ram (parsePerms "rw") little,
      mkRegion "ram8" 0x2000 8 Kind.ram (parsePerms "rw") little ],
    unknownDefault := 0 }

def faultIs {α} (e : Except Fault α) (f : Fault) : Bool :=
  match e with | .error g => g == f | _ => false
def okIs (e : Except Fault Word) (v : Word) : Bool :=
  match e with | .ok x => x == v | _ => false

def checks (little : Bool) : List (String × Bool) :=
  let m := build little
  let (r0, m) := m.busRead 0 32 (fetch := true)            -- rom fixture
  let want : Word := if little then 0x33221100 else 0x00112233
  let (_, m) := m.busWrite 0x1000 0xDEADBEEF 32            -- ram store
  let (r1, m) := m.busRead 0x1000 32                       -- ram reload
  let (r2, m) := m.busRead 0x9000 32                       -- unknown frontier (default)
  let (w0, m) := m.busWrite 0 0 32                         -- write to rom → perm fault
  -- A1: cross-region bounds (ram8 is 8 bytes at 0x2000)
  let (wEnd, m) := m.busWrite 0x2004 0xAA 32               -- off 4, 4..8 → ok
  let (wX, m) := m.busWrite 0x2006 0xBB 32                 -- off 6, 6..10 → cross
  let (rX, _) := m.busRead 0x2005 32                       -- off 5, 5..9 → cross
  [ ("rom_read", okIs r0 want),
    ("ram_roundtrip", okIs r1 0xDEADBEEF),
    ("unknown_frontier_default", okIs r2 0),
    ("rom_write_faults", faultIs w0 Fault.perm),
    ("boundary_write_ok", (match wEnd with | .ok _ => true | _ => false)),
    ("cross_write_faults", faultIs wX Fault.cross),
    ("cross_read_faults", faultIs rX Fault.cross) ]

-- A2: strict-fault unknown policy actually faults.
def faultPolicyChecks : List (String × Bool) :=
  let m : Machine := { (build true) with unknownRead := .fault, unknownWrite := .fault }
  let (r, m) := m.busRead 0x9000 32
  let (w, _) := m.busWrite 0x9000 1 32
  [ ("unknown_read_fault_policy", faultIs r Fault.unknown),
    ("unknown_write_fault_policy", faultIs w Fault.unknown) ]

-- A3: non-overlap decode well-formedness.
def overlapChecks : List (String × Bool) :=
  let good := build true
  let bad : Machine :=
    { regions := #[ mkRegion "a" 0x1000 0x1000 Kind.ram (parsePerms "rw") true,
                    mkRegion "b" 0x1800 0x1000 Kind.ram (parsePerms "rw") true ] }
  [ ("wellformed_accepts_disjoint", good.busWellFormed == true),
    ("wellformed_rejects_overlap", bad.busWellFormed == false) ]

def main : IO Unit := do
  let mut allOk := true
  let all := (checks true).map (fun (n, b) => ("LE " ++ n, b))
           ++ (checks false).map (fun (n, b) => ("BE " ++ n, b))
           ++ faultPolicyChecks ++ overlapChecks
  for (name, ok) in all do
    let st := if ok then "ok" else "FAIL"
    IO.println s!"{name}: {st}"
    if !ok then allOk := false
  if !allOk then throw (IO.userError "core smoke checks failed")
  IO.println "core smoke: PASS"
