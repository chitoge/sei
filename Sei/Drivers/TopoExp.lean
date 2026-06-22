/-
E21 test: ingest a minimal topology (RAM, UART, timer, IRQ) → hardware-entry
descriptor → Machine; MMIO events are named by device; device placement carries
class `unknown` (no behavior); an overlapping-memory topology is rejected.
Exit 0 = pass.
-/
import Sei.Core
import Sei.Hw.Descriptor
import Sei.Hw.Adapter
import Sei.Hw.Topology
open Lean Sei.Core Sei.Hw

def q (s : String) : String := s.replace "'" "\""

def topo : String := q
  "{'name':'board0','arch':'arm','endian':'little','reset_pc':'0x0','memory':[{'name':'ram','base':'0x0','size':'0x100000','kind':'ram','perms':'rwx'}],'devices':[{'name':'uart0','type':'uart','base':'0x40000000','size':'0x100','irq':5},{'name':'timer0','type':'timer','base':'0x40001000','size':'0x100','irq':6}]}"

-- overlapping RAM regions in the topology must be rejected at instantiation.
def badTopo : String := q
  "{'name':'bad','arch':'arm','endian':'little','reset_pc':'0x0','memory':[{'name':'a','base':'0x0','size':'0x2000','kind':'ram','perms':'rw'},{'name':'b','base':'0x1000','size':'0x2000','kind':'ram','perms':'rw'}],'devices':[]}"

def isErr {α} : Except String α → Bool | .error _ => true | .ok _ => false

def topoChecks : Except String (List (String × Bool)) := do
  let m ← loadJson (← topoText topo)
  -- read the UART window → an mmio event named by the device
  let (_, m2) := m.busRead 0x40000000 32
  let namedByDevice := m2.trace.any fun ev => match ev.effect with
    | .mmioRead dev .. => dev == "uart0" | _ => false
  -- device placement is class unknown (topology is not behavior)
  let placementUnknown := m.devices.all (fun d => d.sem.cls == SemClass.unknown)
  pure [ ("instantiates", m.regions.size == 1 && m.devices.size == 2),
         ("wellformed", m.busWellFormed),
         ("mmio_named_by_device", namedByDevice),
         ("placement_is_unknown_class", placementUnknown),
         ("overlapping_topology_rejected", isErr (topoText badTopo >>= loadJson)) ]

def main : IO Unit := do
  match topoChecks with
  | .error e => throw (IO.userError s!"topology ingestion failed: {e}")
  | .ok checks =>
    let mut ok := true
    for (n, b) in checks do
      let tag := if b then "ok" else "FAIL"
      IO.println s!"{n}: {tag}"
      if !b then ok := false
    if !ok then throw (IO.userError "topology checks failed")
    IO.println "topology (E21): PASS"
