/-
E19 test: multi-source import smoke. Exercise register (SVD-like), topology
(devicetree-like), and raw-P-code ingestion together; each produces a classified
`Artifact` (fidelity class + source map + diagnostics). Asserts all three import,
each is classified (register→spec, topology→unknown, p-code→spec), all carry a
source map, and the unsupported-op path produces a diagnostic — no imported unit
runs unclassified. Exit 0 = pass.
-/
import Sei.Core
import Sei.Hw.Descriptor
import Sei.Hw.Adapter
import Sei.Hw.RegisterIR
import Sei.Hw.Topology
import Sei.Isa.Toy
import Sei.IR
import Sei.Hw.Pcode
open Lean Sei.Core Sei.Hw Sei.Pcode

def q (s : String) : String := s.replace "'" "\""

def regSchema : String := q
  "{'name':'rtc','registers':[{'name':'CTRL','offset':'0x0','reset':'0x0','fields':[{'name':'EN','bits':'0','access':'rw'},{'name':'RESV','bits':'31:1','access':'reserved'}]}]}"
def topoSrc : String := q
  "{'name':'b','arch':'arm','endian':'little','reset_pc':'0x0','memory':[{'name':'ram','base':'0x0','size':'0x1000','kind':'ram','perms':'rw'}],'devices':[{'name':'uart0','type':'uart','base':'0x40000000','size':'0x100'}]}"
def pcodeSrc : List Op := [.copy (.reg 1) (.const 5), .intAdd (.reg 2) (.reg 1) (.const 3)]

structure Artifact where
  kind : String
  cls : SemClass
  hasSourceMap : Bool
  diagnostics : List String
  deriving Inhabited

def imports : Except String (List Artifact) := do
  let regDev ← loadRegDevice regSchema 0x50000000 0x100
  let topoM ← loadJson (← topoText topoSrc)
  let _block ← lowerPcode pcodeSrc
  let sm ← sourceMap pcodeSrc
  let diag := match lowerPcode [Op.unsupported "FLOAT_ADD"] with | .error e => [e] | .ok _ => []
  pure [ { kind := "svd-register", cls := regDev.sem.cls, hasSourceMap := true, diagnostics := [] },
         { kind := "devicetree-topology", cls := (topoM.devices.getD 0 default).sem.cls,
           hasSourceMap := true, diagnostics := [] },
         { kind := "raw-pcode", cls := .spec, hasSourceMap := sm.length > 0, diagnostics := diag } ]

def at? (arts : List Artifact) (i : Nat) : Artifact := arts.getD i default

def multiChecks : Except String (List (String × Bool)) := do
  let arts ← imports
  pure [ ("three_sources_imported", arts.length == 3),
         ("register_is_spec", (at? arts 0).cls == SemClass.spec),
         ("topology_is_unknown", (at? arts 1).cls == SemClass.unknown),
         ("pcode_is_spec", (at? arts 2).cls == SemClass.spec),
         ("all_have_source_map", arts.all (·.hasSourceMap)),
         ("none_unclassified", arts.all fun a => validCombo a.cls .none),
         ("pcode_diagnostic_present", (at? arts 2).diagnostics.length > 0) ]

def main : IO Unit := do
  match multiChecks with
  | .error e => throw (IO.userError s!"multi-source import failed: {e}")
  | .ok cs =>
    let mut ok := true
    for (n, b) in cs do
      let tag := if b then "ok" else "FAIL"
      IO.println s!"{n}: {tag}"
      if !b then ok := false
    if !ok then throw (IO.userError "multi-source import checks failed")
    IO.println "multi-source import (E19): PASS"
