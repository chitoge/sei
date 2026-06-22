/-
E06 producer adapter (Lean): convert a shadowrealm `model-*.json` evidence file
into a SEI hardware-entry descriptor (`Json`). Consumer-layer tooling — the
output is consumed by `Sei.Hw.loadMachine`. Firmware blobs are never embedded;
`memory[].src` becomes a descriptor `image` reference only.
-/
import Lean.Data.Json
open Lean

namespace Sei.Hw.Adapter

def jstr (s : String) : Json := Json.str s
def jarr (xs : List Json) : Json := Json.arr xs.toArray
def jobj (xs : List (String × Json)) : Json := Json.mkObj xs
def jnum (mantissa : Int) (exponent : Nat) : Json := Json.num { mantissa := mantissa, exponent := exponent }

/-- A standard `irq_time` block (schema-required; topology, not behavior). -/
def irqTimeObj : Json :=
  jobj [("clock_source", jstr "unknown"), ("controller", jstr "unknown"),
        ("reset_lines", jarr []), ("scheduling_mode", jstr "deterministic"),
        ("timer_source", jstr "unknown")]

/-- Top-level keys the descriptor schema requires. -/
def requiredTopKeys : List String :=
  ["version", "cpu", "entry", "memory", "mmio", "irq_time", "trace_snapshot", "provenance"]

/-- Lean-equivalent schema conformance: every required top-level key is present
    and `provenance.confidence` is a JSON number (not a string). -/
def schemaConformant (j : Json) : Bool :=
  requiredTopKeys.all (fun k => (j.getObjVal? k).toOption.isSome) &&
  (match (j.getObjVal? "provenance").bind (·.getObjVal? "confidence") with
   | .ok (.num _) => true | _ => false)

/-- shadowrealm arch tag → (descriptor arch, endian). -/
def archMap : String → String × String
  | "armle"    => ("arm", "little")
  | "armbe"    => ("arm", "big")
  | "mips32le" => ("mips32", "little")
  | a          => (a, "little")

def getStr (j : Json) (k : String) (dflt : String) : String :=
  ((j.getObjVal? k).bind (·.getStr?)).toOption.getD dflt

def getArr (j : Json) (k : String) : List Json :=
  (((j.getObjVal? k).bind (·.getArr?)).toOption).getD #[] |>.toList

/-- Enumerate an object's `(key, value)` entries (e.g. the `peripherals` map). -/
def objEntries : Json → List (String × Json)
  | .obj kvs => kvs.toList
  | _ => []

def strList (j : Json) (k : String) : List String :=
  (getArr j k).filterMap (·.getStr?.toOption)

/-- Kind for a shadowrealm memory `type`. -/
def kindOf : String → String
  | "rom" => "rom" | "rom-mirror" => "alias" | _ => "ram"

/-- Convert a model JSON into a descriptor JSON. -/
def adapt (model : Json) (source : String) : Json :=
  let (arch, endian) := archMap (getStr model "arch" "unknown")
  let entry := getStr model "entry" "0x0"
  let quirks := strList model "cpu_quirks"
  -- first rom region name, for rom-mirror aliases
  let mems := getArr model "memory"
  let romName : Option String := (mems.zipIdx.find? (fun (m, _) =>
    getStr m "type" "" == "rom")).map (fun (_, i) => s!"rom{i}")
  let regions := mems.zipIdx.map fun (m, i) =>
    let ty := getStr m "type" "ram"
    let kind := kindOf ty
    let nm := s!"{ty.replace "-" ""}{i}"
    let perms := if kind == "ram" then "rw" else "rx"
    let base := [("name", jstr nm), ("base", jstr (getStr m "base" "0x0")),
                 ("size", jstr (getStr m "size" "0x0")), ("kind", jstr kind),
                 ("perms", jstr perms),
                 ("provenance", jstr s!"{source}: {getStr m "note" ty}")]
    let withSrc := match (m.getObjVal? "src").toOption.bind (·.getStr?.toOption) with
      | some src => base ++ [("image", jstr src)] | none => base
    let withAlias := if kind == "alias" then
        withSrc ++ [("alias_of", jstr (romName.getD nm))] else withSrc
    jobj withAlias
  let windows := (strList model "mmio_windows").zipIdx.map fun (w, i) =>
    jobj [("name", jstr s!"mmio{i}"), ("base", jstr w), ("size", jstr "0x10000"),
          ("side_effect_policy", jstr "unknown-stub")]
  let devices := (objEntries (((model.getObjVal? "peripherals").toOption).getD (Json.mkObj []))).map
    fun (addr, p) =>
      let cls := getStr p "class" "unknown"
      let val := getStr p "value" "0x0"
      jobj [("name", jstr s!"periph_{addr.replace "0x" ""}"), ("type", jstr cls),
            ("base", jstr addr), ("size", jstr "0x4"),
            ("schema", jobj [("registers", jarr
              [jobj [("offset", jstr "0x0"), ("reset", jstr val)]])]),
            ("provenance", jstr s!"{source}: class={cls}")]
  jobj [
    ("version", jstr "sei-hw-entry/0"),
    ("cpu", jobj [("arch", jstr arch), ("endian", jstr endian),
                  ("instr_mode", jstr arch), ("privilege_mode", jstr "svc"),
                  ("features", jarr (quirks.map jstr)),
                  ("reset_quirks", jarr (quirks.map jstr))]),
    ("entry", jobj [("reset_pc", jstr entry), ("vector_base", jstr entry),
                    ("exception_state", jstr "svc"), ("reg_overrides", jobj [])]),
    ("memory", jarr regions),
    ("mmio", jobj [("windows", jarr windows),
      ("default_unknown_policy", jobj [("on_read", jstr "default-value"),
        ("value", jstr (getStr model "mmio_default" "0x0")), ("on_write", jstr "log-drop")])]),
    ("devices", jarr devices),
    ("irq_time", irqTimeObj),
    ("trace_snapshot", jobj [("trace_channels", jarr [jstr "exec", jstr "mem_read"])]),
    ("provenance", jobj [("source", jstr source), ("confidence", jnum 7 1),
                         ("notes", jstr (getStr model "provenance" ""))])
  ]

/-- Adapt model text → descriptor text (compressed JSON). -/
def adaptText (modelText source : String) : Except String String := do
  pure (adapt (← Json.parse modelText) source).compress

end Sei.Hw.Adapter
