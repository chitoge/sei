/-
E06 adapter test (Lean): adapt representative shadowrealm model JSON to a SEI
descriptor and confirm the descriptor instantiates a Machine with the expected
region/device counts (so the producer side is validated end-to-end without the
external corpus). Exit 0 = pass.
-/
import Sei.Core
import Sei.Hw.Descriptor
import Sei.Hw.Adapter
open Lean Sei.Core Sei.Hw Sei.Hw.Adapter

def q (s : String) : String := s.replace "'" "\""

def bro1Model : String := q
  "{'arch':'armle','entry':'0x40','memory':[{'base':'0x0','size':'0x1000000','type':'rom','src':'bro1.rom'},{'base':'0xe0000000','size':'0x1000000','type':'rom-mirror','src':'bro1.rom'},{'base':'0xce000000','size':'0x800000','type':'ram'}],'cpu_quirks':['mmu-bypass','vfp'],'mmio_windows':['0xcc000000','0xd0000000'],'mmio_default':'0x0','peripherals':{'0xd0d00400':{'class':'increasing-timer'},'0xd0b0000c':{'class':'const','value':'0x80000000'}}}"

def sonyModel : String := q
  "{'arch':'armbe','entry':'0x0','memory':[{'base':'0x0','size':'0x1000000','type':'rom','src':'sony_main_16.bin'},{'base':'0xb0000000','size':'0x8000000','type':'ram'}],'cpu_quirks':['mmu-bypass','vfp'],'mmio_windows':['0x3c000000'],'mmio_default':'0x0','peripherals':{}}"

def check (model source : String) (expR expD : Nat) : Except String (Nat × Nat × Bool) := do
  let descText ← adaptText model source
  let conformant := match Json.parse descText with | .ok j => schemaConformant j | _ => false
  let m ← loadJson descText
  pure (m.regions.size, m.devices.size,
        m.regions.size == expR && m.devices.size == expD && m.busWellFormed && conformant)

-- devices = peripherals + mmio windows lowered to stubs (finding 2)
def cases : List (String × String × Nat × Nat) :=
  [ ("bro1", bro1Model, 3, 4), ("sony", sonyModel, 2, 1) ]

-- A descriptor missing the schema-required irq_time must be flagged non-conformant.
def nonConformant : Bool :=
  match Json.parse (q "{'cpu':{'arch':'arm','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[],'mmio':{},'version':'sei-hw-entry/0','trace_snapshot':{},'provenance':{'confidence':0.5}}") with
  | .ok j => schemaConformant j == false   -- missing irq_time
  | _ => false

def main : IO Unit := do
  let mut ok := true
  for (name, model, expR, expD) in cases do
    match check model name expR expD with
    | .error e => IO.println s!"{name}: FAIL — {e}"; ok := false
    | .ok (r, d, good) =>
      let tag := if good then "ok" else "FAIL"
      IO.println s!"{name}: regions={r} devices={d} schema_conformant {tag}"
      if !good then ok := false
  let ncTag := if nonConformant then "ok" else "FAIL"
  IO.println s!"non_conformant_rejected: {ncTag}"
  if !nonConformant then ok := false
  if !ok then throw (IO.userError "adapter failed")
  IO.println "adapter: PASS"
