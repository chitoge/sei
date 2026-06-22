/-
L1 (large-use-case plan): firmware intake → hardware-entry descriptor. A checked
intake manifest (CPU family guess + optional evidence-backed hints) is turned
into a `.sei.json` descriptor without hand-built Lean fixtures. Guessed facts are
kept `derived`/`unknown` (never promoted as `spec`); bad/incomplete intake fails
closed with a diagnostic.
-/
import Lean.Data.Json
import Sei.Hw.Descriptor
import Sei.Hw.Adapter
open Lean Sei.Core Sei.Hw Sei.Hw.Adapter
namespace Sei.Hw

/-- A memory region object from a `{base,size,image?}` manifest node. -/
def regionObj (nm : Json) (kind perms : String) : Json :=
  let base := [("name", jstr (getStr nm "name" (if kind == "rom" then "rom" else "ram"))),
               ("base", jstr (getStr nm "base" "0x0")), ("size", jstr (getStr nm "size" "0x0")),
               ("kind", jstr kind), ("perms", jstr perms), ("provenance", jstr "intake")]
  match (nm.getObjVal? "image").toOption.bind (·.getStr?.toOption) with
  | some i => jobj (base ++ [("image", jstr i)])
  | none => jobj base

/-- Manifest JSON → hardware-entry descriptor JSON (fails closed). -/
def manifestToDescriptor (man : Json) : Except String Json := do
  let arch ← (man.getObjVal? "arch").bind (·.getStr?)
  let cpuArch := if arch == "thumb" then "arm" else arch
  if cpuArch != "arm" && cpuArch != "mips32" then
    throw s!"intake: unsupported arch '{arch}' (want arm|mips32|thumb)"
  let endian := getStr man "endian" "little"
  let entry ← man.getObjVal? "entry"
  let resetPc := getStr entry "reset_pc" "0x0"
  let mem ← man.getObjVal? "memory"
  let rom ← mem.getObjVal? "rom"
  let ram ← mem.getObjVal? "ram"
  let windows := (strList man "mmio_windows").zipIdx.map fun (w, i) =>
    jobj [("name", jstr s!"mmio{i}"), ("base", jstr w), ("size", jstr "0x10000"),
          ("side_effect_policy", jstr "unknown-stub")]
  let evidence := strList man "evidence"          -- facts that are evidence-backed
  let quirks := if arch == "thumb" then [jstr "thumb"] else []
  pure <| jobj [
    ("version", jstr "sei-hw-entry/0"),
    ("cpu", jobj [("arch", jstr cpuArch), ("endian", jstr endian), ("instr_mode", jstr arch),
                  ("privilege_mode", jstr "svc"), ("features", jarr quirks),
                  ("reset_quirks", jarr quirks)]),
    ("entry", jobj [("reset_pc", jstr resetPc), ("vector_base", jstr (getStr entry "vector_base" resetPc)),
                    ("sp", jstr (getStr entry "sp" "0x0")), ("exception_state", jstr "none"),
                    ("reg_overrides", jobj [])]),
    ("memory", jarr [regionObj rom "rom" "rx", regionObj ram "ram" "rw"]),
    ("mmio", jobj [("windows", jarr windows),
      ("default_unknown_policy", jobj [("on_read", jstr "default-value"),
        ("value", jstr "0x0"), ("on_write", jstr "log-drop")])]),
    ("irq_time", irqTimeObj),
    ("trace_snapshot", jobj [("trace_channels", jarr [jstr "exec", jstr "mem_read", jstr "mmio_read"]),
      ("validation_goals", jarr [jstr "instantiates", jstr "runs to a typed frontier"])]),
    -- evidence-backed facts vs guesses are recorded; guessed values stay derived.
    ("provenance", jobj [("source", jstr (getStr (man.getObjVal? "source" |>.toOption.getD (jobj [])) "path" "unknown")),
                         ("confidence", jnum 5 1),
                         ("derived_from", jarr (evidence.map jstr)),
                         ("notes", jstr "intake: facts not in derived_from are guesses (derived/unknown)")])
  ]

/-- Manifest text + images → Machine (via the descriptor path). -/
def intakeMachine (manText : String) (images : List (String × ByteArray) := []) : Except String Machine := do
  loadMachine (← parseDescriptor (← manifestToDescriptor (← Json.parse manText))) images

end Sei.Hw
