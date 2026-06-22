/-
Hardware-entry descriptor ingestion in Lean (audit N1 / B1): parse a `.sei.json`
descriptor, validate it, and instantiate a `Sei.Core.Machine` — the Lean
counterpart of the removed Python `descriptor.py::load_machine`.

`loadMachine` **fails closed**: a dangling alias, or a descriptor whose regions
or device windows overlap (ambiguous decode, audit A3), is rejected.
-/
import Lean.Data.Json
import Sei.Core
open Lean Sei.Core

namespace Sei.Hw

/-! ### Parsed descriptor (only what machine construction needs) -/

structure RegionD where
  name : String
  base : Nat
  size : Nat
  kind : Kind
  perms : Nat
  aliasOf : Option String
  image : Option String
  gated : Bool := false      -- starts off the bus until its controller enables it (L4)

structure RegD where
  offset : Nat
  reset : Word

structure DeviceD where
  name : String
  base : Nat
  size : Nat
  regs : List RegD
  sem : SemanticsMeta
  type : String := ""        -- controller class: ddr | watchdog | uart | ...
  gates : String := ""       -- (ddr) the memory region this controller gates
  timeout : Nat := 0         -- (watchdog) fire threshold
  policy : String := ""      -- (watchdog) disabled | serviced | reset
  step : Nat := 0x1000       -- (increasing-timer) per-read increment

structure WindowD where
  name : String
  base : Nat
  size : Nat

structure HwEntry where
  arch : String
  little : Bool
  resetPc : Nat
  highVectors : Bool
  sp : Nat := 0                          -- entry.sp (initial stack pointer)
  exceptionState : String := "none"      -- entry.exception_state (e.g. "thumb")
  regOverrides : List (Nat × Word) := [] -- entry.reg_overrides (rN → value)
  regions : List RegionD
  unknownDefault : Word
  unknownRead : UnknownPolicy
  unknownWrite : UnknownPolicy
  devices : List DeviceD
  windows : List WindowD

/-! ### JSON helpers -/

def hexDigit (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
  else .error s!"bad hex digit '{c}'"

/-- Parse a `"0x.."` hex string or a decimal string to a `Nat`. -/
def parseHexNat (s : String) : Except String Nat :=
  if s.startsWith "0x" ∨ s.startsWith "0X" then
    (s.toList.drop 2).foldl (fun acc c => acc.bind fun n => (hexDigit c).map (n * 16 + ·)) (.ok 0)
  else match s.toNat? with
    | some n => .ok n
    | none => .error s!"bad number: {s}"

def jStr (j : Json) (k : String) : Except String String := (j.getObjVal? k).bind (·.getStr?)
def jHex (j : Json) (k : String) : Except String Nat := (jStr j k).bind parseHexNat
def jStrOpt (j : Json) (k : String) : Option String := (jStr j k).toOption
def jObjOpt (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
def jArrOpt (j : Json) (k : String) : Array Json :=
  (((j.getObjVal? k).bind (·.getArr?)).toOption).getD #[]

def parseKind : String → Except String Kind
  | "rom" => .ok .rom | "ram" => .ok .ram | "alias" => .ok .alias
  | s => .error s!"bad memory kind: {s}"

-- Fail-closed enum parsers: an unknown value is a diagnostic, not a silent default.
def parsePolicy : String → Except String UnknownPolicy
  | "fault" => .ok .fault
  | "default-value" => .ok .defaultValue
  | "log-drop" => .ok .defaultValue
  | s => .error s!"invalid unknown-MMIO policy: {s}"

/-! ### Parser -/

def parseRegion (j : Json) : Except String RegionD := do
  let name ← jStr j "name"
  let base ← jHex j "base"
  let size ← jHex j "size"
  let kind ← parseKind (← jStr j "kind")
  let perms := parsePerms (← jStr j "perms")
  pure { name, base, size, kind, perms,
         aliasOf := jStrOpt j "alias_of", image := jStrOpt j "image",
         gated := ((j.getObjVal? "gated").bind (·.getBool?)).toOption.getD false }

def parseSemClass : String → Except String SemClass
  | "spec" => .ok .spec | "derived" => .ok .derived | "observational" => .ok .observational
  | "traceReplay" => .ok .traceReplay | "external" => .ok .external | "unknown" => .ok .unknown
  | s => .error s!"invalid semantic class: {s}"

def parseProofUse : String → Except String ProofUse
  | "full" => .ok .full | "local" => .ok .local
  | "translation-validation" => .ok .translationValidation | "none" => .ok .none
  | s => .error s!"invalid proof_use: {s}"

def parseDevice (j : Json) : Except String DeviceD := do
  let name ← jStr j "name"
  let base ← jHex j "base"
  let size ← jHex j "size"
  let regsJson := match jObjOpt j "schema" with | some sj => jArrOpt sj "registers" | none => #[]
  let regs ← regsJson.toList.mapM fun r => do
    pure ({ offset := (← jHex r "offset"), reset := BitVec.ofNat 32 (← jHex r "reset") } : RegD)
  -- Optional declared fidelity (workflow Stage 4); invalid values fail closed.
  let sem ← match jObjOpt j "semantics" with
    | some sj => do
      let cls ← parseSemClass ((jStrOpt sj "class").getD "unknown")
      let pu ← parseProofUse ((jStrOpt sj "proof_use").getD "none")
      pure ({ id := (jStrOpt sj "id").getD name, cls := cls, proofUse := pu,
              source := (jStrOpt sj "source").getD "" } : SemanticsMeta)
    | none => pure ({ id := name, cls := .unknown } : SemanticsMeta)
  pure { name, base, size, regs, sem,
         type := (jStrOpt j "type").getD "", gates := (jStrOpt j "gates").getD "",
         timeout := ((jHex j "timeout").toOption).getD 0, policy := (jStrOpt j "policy").getD "",
         step := ((jHex j "step").toOption).getD 0x1000 }

def parseDescriptor (j : Json) : Except String HwEntry := do
  let cpu ← j.getObjVal? "cpu"
  let arch ← jStr cpu "arch"
  let endian ← jStr cpu "endian"
  if endian != "little" && endian != "big" then throw s!"invalid endian: {endian}"
  let little := endian == "little"
  let entry ← j.getObjVal? "entry"
  let resetPc ← jHex entry "reset_pc"
  let sp := ((jHex entry "sp").toOption).getD 0
  let exceptionState := (jStrOpt entry "exception_state").getD "none"
  -- reg_overrides: an object { "rN" | "N" : "0x..." } applied at reset
  let regOverrides : List (Nat × Word) := match jObjOpt entry "reg_overrides" with
    | some (.obj kvs) => kvs.toList.filterMap fun (k, v) =>
        match (k.stripPrefix "r").toNat?, v.getStr?.toOption.bind (parseHexNat · |>.toOption) with
        | some i, some n => some (i, BitVec.ofNat 32 n) | _, _ => none
    | _ => []
  let quirks := (jArrOpt cpu "features" ++ jArrOpt cpu "reset_quirks").toList.filterMap
    (·.getStr?.toOption)
  let highVectors := quirks.contains "highvecs" || quirks.contains "high-vectors"
    || ((jStrOpt entry "vector_base").getD "") == "0xffff0000"
  let regions ← (jArrOpt j "memory").toList.mapM parseRegion
  let pol ← (← j.getObjVal? "mmio").getObjVal? "default_unknown_policy"
  let unknownDefault := BitVec.ofNat 32 (← jHex pol "value")
  let unknownRead ← parsePolicy (← jStr pol "on_read")
  let unknownWrite ← parsePolicy (← jStr pol "on_write")
  let devices ← (jArrOpt j "devices").toList.mapM parseDevice
  let mmio ← j.getObjVal? "mmio"
  let windows ← (jArrOpt mmio "windows").toList.mapM fun w => do
    pure ({ name := (← jStr w "name"), base := (← jHex w "base"), size := (← jHex w "size") } : WindowD)
  pure { arch, little, resetPc, highVectors, sp, exceptionState, regOverrides, regions,
         unknownDefault, unknownRead, unknownWrite, devices, windows }

/-! ### Instantiation (fails closed) -/

def loadMachine (h : HwEntry) (images : List (String × ByteArray) := []) : Except String Machine := do
  let names := h.regions.map (·.name)
  for r in h.regions do
    if r.kind == Kind.alias then
      match r.aliasOf with
      | none => throw s!"alias region {r.name} missing alias_of"
      | some t => if ¬ names.contains t then throw s!"alias {r.name} targets unknown region {t}"
  -- E14: reject any device whose declared fidelity is an invalid class/proof-use combo.
  for d in h.devices do
    if ¬ d.sem.valid then
      throw s!"device {d.name}: invalid fidelity combo (class/proof_use)"
  let regions := (h.regions.map fun r =>
    let img := match r.image with
      | some name => (images.find? (·.1 == name)).map (·.2) |>.getD ByteArray.empty
      | none => ByteArray.empty
    { mkRegion r.name r.base r.size r.kind r.perms h.little img r.aliasOf with enabled := ¬ r.gated }).toArray
  -- L4: instantiate a controller behavior from the device `type`, else a stub.
  let behOf (d : DeviceD) : DevBehavior :=
    match d.type with
    | "ddr" => .ddr false d.gates
    | "watchdog" => .watchdog 0 d.timeout d.policy
    | "increasing-timer" => .external d.name 0 (BitVec.ofNat 32 d.step)   -- free-running counter (#7)
    -- "const"/"status" lower to a reg stub whose reset is the constant value (#7)
    | _ => .regStub (d.regs.map fun rg => (rg.offset, rg.reset))
  let devs := h.devices.map fun d =>
    ({ name := d.name, base := d.base, size := d.size, beh := behOf d, sem := d.sem } : Device)
  -- finding 2: lower each MMIO window not already covered by a device to an
  -- unknown-class stub so it participates in overlap checks and emits named effects.
  let devBases := devs.map (·.base)
  let windowDevs := (h.windows.filter (fun w => ¬ devBases.contains w.base)).map fun w =>
    ({ name := w.name, base := w.base, size := w.size, beh := .regStub [],
       sem := { id := w.name, cls := .unknown, proofUse := .none,
                source := "descriptor mmio window" } } : Device)
  let devices := (devs ++ windowDevs).toArray
  let m : Machine :=
    { regions, devices, unknownDefault := h.unknownDefault,
      unknownRead := h.unknownRead, unknownWrite := h.unknownWrite }
  if ¬ m.busWellFormed then
    throw "descriptor instantiates an ambiguous bus (overlapping regions or device windows)"
  pure m

/-- Convenience: JSON text → Machine. -/
def loadJson (text : String) : Except String Machine := do
  loadMachine (← parseDescriptor (← Json.parse text))

end Sei.Hw
