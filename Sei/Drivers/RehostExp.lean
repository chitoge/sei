/-
L1+L2 test (firmware rehosting path): an intake manifest for an ARM, a MIPS, and
a Thumb sample image is turned into a descriptor (no hand-built fixture), each
instantiates a Machine, and the bounded runner executes it to a typed stop with a
deterministic report. Bad intake fails closed. Exit 0 = pass.
-/
import Sei.Core
import Sei.Hw.Descriptor
import Sei.Hw.Adapter
import Sei.Hw.Intake
import Sei.Hw.Runner
import Sei.Isa.Arm
import Sei.Isa.Mips
open Lean Sei.Core Sei.Hw Sei.Hw.Adapter

def q (s : String) : String := s.replace "'" "\""

def armMan : String := q
  "{'arch':'arm','endian':'little','entry':{'reset_pc':'0x0','sp':'0x100000'},'memory':{'rom':{'base':'0x0','size':'0x1000','image':'fw'},'ram':{'base':'0x100000','size':'0x100000'}},'mmio_windows':['0x40000000'],'evidence':['arch','entry.reset_pc'],'source':{'path':'arm.bin'}}"
def mipsMan : String := q
  "{'arch':'mips32','endian':'little','entry':{'reset_pc':'0x80000000'},'memory':{'rom':{'base':'0x0','size':'0x1000','image':'fw'},'ram':{'base':'0x1000','size':'0x1000'}},'evidence':['arch'],'source':{'path':'mips.bin'}}"
def thumbMan : String := q
  "{'arch':'thumb','endian':'little','entry':{'reset_pc':'0x0'},'memory':{'rom':{'base':'0x0','size':'0x1000','image':'fw'},'ram':{'base':'0x100000','size':'0x1000'}},'evidence':['arch'],'source':{'path':'thumb.bin'}}"
def badMan : String := q
  "{'arch':'x86','endian':'little','entry':{'reset_pc':'0x0'},'memory':{'rom':{'base':'0x0','size':'0x1000'},'ram':{'base':'0x1000','size':'0x1000'}}}"

-- sample firmware: each ends at a frontier (self-branch) or polls unknown MMIO.
def armFw : ByteArray := bytesToBA (Sei.Isa.Arm.assemble [Sei.Isa.Arm.MOVW 0 0, Sei.Isa.Arm.B 0x4 0x4] true)
-- L5 coverage: a program with an undecoded A32 word (coprocessor space)
def armCovMan : String := q
  "{'arch':'arm','endian':'little','entry':{'reset_pc':'0x0'},'memory':{'rom':{'base':'0x0','size':'0x1000','image':'fw'},'ram':{'base':'0x100000','size':'0x1000'}},'evidence':['arch'],'source':{'path':'armcov.bin'}}"
def armCovFw : ByteArray := bytesToBA (Sei.Isa.Arm.assemble [Sei.Isa.Arm.MOVW 0 0, (0xEC000000 : Word)] true)
def thumbFw : ByteArray := bytesToBA (encodeBytes true 0x2105 2 ++ encodeBytes true 0xe7fe 2)  -- MOVS r1,#5 ; B .
def mipsFw : ByteArray := (Id.run do
  let prog := [Sei.Isa.Mips.LUI 2 0xBF00, Sei.Isa.Mips.LW 1 0 2, Sei.Isa.Mips.BEQ 0 0 0x8 0x8]
  let mut buf : Array Byte := (List.replicate 0x1000 (0 : Byte)).toArray
  for (w, i) in prog.zipIdx do
    let bs := encodeBytes true w.toNat 4
    for k in [0:4] do buf := buf.setIfInBounds (i * 4 + k) (bs.getD k 0)
  return bytesToBA buf.toList)

def isErr {α} : Except String α → Bool | .error _ => true | .ok _ => false

def runs : Except String (List (String × Bool)) := do
  let armR ← runManifest armMan [("fw", armFw)] 50
  let mipsR ← runManifest mipsMan [("fw", mipsFw)] 50
  let thumbR ← runManifest thumbMan [("fw", thumbFw)] 50
  let armR2 ← runManifest armMan [("fw", armFw)] 50
  let covR ← runManifest armCovMan [("fw", armCovFw)] 30
  -- generated descriptor is schema-conformant + records evidence
  let armDesc ← manifestToDescriptor (← Json.parse armMan)
  let evidenceRecorded := match (armDesc.getObjVal? "provenance").bind (·.getObjVal? "derived_from") with
    | .ok (.arr a) => a.size > 0 | _ => false
  pure
    [ ("arm_runs_to_frontier", armR.stop == StopReason.blockedFrontier && armR.arch == "arm"),
      ("mips_hits_unknown_mmio", mipsR.stop == StopReason.unknownMmio && mipsR.arch == "mips32"),
      ("thumb_runs_to_frontier", thumbR.stop == StopReason.blockedFrontier && thumbR.arch == "thumb"),
      ("report_has_regions_devices", armR.regions == 2 && armR.devices == 1),
      ("deterministic_rerun", armR == armR2),
      ("bad_arch_fails_closed", isErr (runManifest badMan [] 10)),
      ("schema_conformant_descriptor", schemaConformant armDesc),
      ("evidence_recorded", evidenceRecorded),
      -- L5: unsupported-instruction coverage in the report
      ("unsupported_recorded", covR.stop == StopReason.unsupportedInstr && covR.unsupported.length ≥ 1),
      ("unsupported_has_mnem", match covR.unsupported with | (_, _, mn) :: _ => mn == "UNDEF" | [] => false),
      ("descriptor_id_recorded", covR.descriptorId == "armcov.bin") ]

def main : IO Unit := do
  match runs with
  | .error e => throw (IO.userError s!"rehost path failed: {e}")
  | .ok cs =>
    let mut ok := true
    for (n, b) in cs do
      let tag := if b then "ok" else "FAIL"
      IO.println s!"{n}: {tag}"
      if !b then ok := false
    if !ok then throw (IO.userError "rehost checks failed")
    IO.println "firmware rehost path (L1+L2): PASS"
