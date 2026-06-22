/-
E21: topology-source ingestion. Convert a devicetree/Renode-`.repl`-like topology
(memory + device placement + IRQ wiring) into a SEI hardware-entry descriptor.

Topology is *placement, not behavior*: every device becomes an `unknown`-class
register stub (no register semantics invented); device placement and device
behavior stay separate records. The descriptor's bus non-overlap check
(`busWellFormed`) rejects overlapping/ambiguous topology.
-/
import Lean.Data.Json
import Sei.Hw.Descriptor
import Sei.Hw.Adapter
open Lean Sei.Core Sei.Hw Sei.Hw.Adapter
namespace Sei.Hw

/-- A devicetree/Renode-like topology JSON → SEI descriptor JSON. -/
def topoToDescriptor (topo : Json) : Json :=
  let arch := getStr topo "arch" "arm"
  let endian := getStr topo "endian" "little"
  let resetPc := getStr topo "reset_pc" "0x0"
  let mem := (getArr topo "memory").map fun m =>
    jobj [("name", jstr (getStr m "name" "ram")), ("base", jstr (getStr m "base" "0x0")),
          ("size", jstr (getStr m "size" "0x0")), ("kind", jstr (getStr m "kind" "ram")),
          ("perms", jstr (getStr m "perms" "rwx")), ("provenance", jstr "topology")]
  let devs := (getArr topo "devices")
  let windows := devs.map fun d =>
    jobj [("name", jstr (getStr d "name" "dev")), ("base", jstr (getStr d "base" "0x0")),
          ("size", jstr (getStr d "size" "0x0")), ("side_effect_policy", jstr "unknown-stub")]
  let deviceRecs := devs.map fun d =>
    jobj [("name", jstr (getStr d "name" "dev")), ("type", jstr (getStr d "type" "unknown")),
          ("base", jstr (getStr d "base" "0x0")), ("size", jstr (getStr d "size" "0x0")),
          -- placement only: behavior is unknown until a separate behavior artifact.
          ("semantics", jobj [("class", jstr "unknown"), ("proof_use", jstr "none"),
                              ("source", jstr "topology placement (no behavior)")]),
          ("schema", jobj [("registers", jarr [])])]
  jobj [
    ("version", jstr "sei-hw-entry/0"),
    ("cpu", jobj [("arch", jstr arch), ("endian", jstr endian), ("instr_mode", jstr arch),
                  ("privilege_mode", jstr "svc"), ("features", jarr []), ("reset_quirks", jarr [])]),
    ("entry", jobj [("reset_pc", jstr resetPc), ("vector_base", jstr resetPc),
                    ("exception_state", jstr "none"), ("reg_overrides", jobj [])]),
    ("memory", jarr mem),
    ("mmio", jobj [("windows", jarr windows),
      ("default_unknown_policy", jobj [("on_read", jstr "default-value"),
        ("value", jstr "0x0"), ("on_write", jstr "log-drop")])]),
    ("devices", jarr deviceRecs),
    ("irq_time", irqTimeObj),
    ("trace_snapshot", jobj [("trace_channels", jarr [jstr "exec", jstr "mmio_read"])]),
    ("provenance", jobj [("source", jstr (getStr topo "name" "topology")),
                         ("confidence", jnum 8 1), ("notes", jstr "from topology source")])
  ]

def topoText (text : String) : Except String String := do
  pure (topoToDescriptor (← Json.parse text)).compress

end Sei.Hw
