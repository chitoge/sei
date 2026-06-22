/-
E00/E06 (Lean): ingest hardware-entry descriptors. Reads the committed
`.sei.json` files passed as argv, round-trips + validates + instantiates each
into a Sei.Core.Machine, and runs embedded negative tests proving validation
fails closed (overlap rejected, dangling alias rejected, fault policy faults).
Exit 0 = all good.
-/
import Sei.Core
import Sei.Hw.Descriptor
open Lean Sei.Core Sei.Hw

def hasSub (hay needle : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- Expected (regions, devices) per known descriptor. -/
-- devices = modeled devices + descriptor mmio windows lowered to stubs (finding 2)
def expectedFor (path : String) : Option (Nat × Nat) :=
  if hasSub path "toy-machine" then some (3, 1)          -- device timer0 == window timer0 (deduped)
  else if hasSub path "classic-arm-be" then some (3, 0)  -- no windows
  else if hasSub path "model-bro1" then some (3, 8)       -- 2 periph + 6 windows
  else if hasSub path "model-sony" then some (3, 8)       -- 0 periph + 8 windows
  else none

def roundTrips (text : String) : Bool :=
  match Json.parse text with
  | .ok j => match Json.parse j.compress with
             | .ok j2 => j.compress == j2.compress
             | .error _ => false
  | .error _ => false

def isErr {α} : Except String α → Bool | .error _ => true | .ok _ => false

/-- Single-quoted JSON → real JSON (avoids escaping every `"` in a Lean literal). -/
def q (s : String) : String := s.replace "'" "\""

def overlapJson : String := q
  "{'cpu':{'arch':'x','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'a','base':'0x0','size':'0x2000','kind':'ram','perms':'rw'},{'name':'b','base':'0x1000','size':'0x2000','kind':'ram','perms':'rw'}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}}}"

def danglingJson : String := q
  "{'cpu':{'arch':'x','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'rom','base':'0x0','size':'0x1000','kind':'rom','perms':'rx'},{'name':'al','base':'0x8000','size':'0x1000','kind':'alias','perms':'rx','alias_of':'nope'}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}}}"

def faultJson : String := q
  "{'cpu':{'arch':'x','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'ram','base':'0x0','size':'0x1000','kind':'ram','perms':'rw'}],'mmio':{'default_unknown_policy':{'on_read':'fault','value':'0x0','on_write':'fault'}}}"

-- (1) a device window that shadows a memory region must be rejected.
def devMemJson : String := q
  "{'cpu':{'arch':'x','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'ram','base':'0x0','size':'0x1000','kind':'ram','perms':'rw'}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}},'devices':[{'name':'d','base':'0x500','size':'0x10','schema':{'registers':[{'offset':'0x0','reset':'0x0'}]}}]}"

-- Fail-closed parsers: invalid enum values are diagnostics, not silent defaults.
def baseMem : String := "'memory':[{'name':'ram','base':'0x0','size':'0x1000','kind':'ram','perms':'rw'}]"
def invalidEndianJson : String := q
  ("{'cpu':{'arch':'x','endian':'middle'},'entry':{'reset_pc':'0x0'}," ++ baseMem ++ ",'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}}}")
def invalidPolicyJson : String := q
  ("{'cpu':{'arch':'x','endian':'little'},'entry':{'reset_pc':'0x0'}," ++ baseMem ++ ",'mmio':{'default_unknown_policy':{'on_read':'perhaps','value':'0x0','on_write':'log-drop'}}}")
def invalidClassJson : String := q
  ("{'cpu':{'arch':'x','endian':'little'},'entry':{'reset_pc':'0x0'}," ++ baseMem ++ ",'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}},'devices':[{'name':'d','base':'0x40000000','size':'0x10','semantics':{'class':'madeup'},'schema':{'registers':[]}}]}")

-- Finding 2: two overlapping mmio windows are an ambiguous decode and rejected.
def windowOverlapJson : String := q
  "{'cpu':{'arch':'x','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'ram','base':'0x0','size':'0x1000','kind':'ram','perms':'rw'}],'mmio':{'windows':[{'name':'w0','base':'0x40000000','size':'0x10000'},{'name':'w1','base':'0x40008000','size':'0x10000'}],'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}}}"

-- Finding 3: an alias whose decode window overlaps a memory region is rejected.
def aliasOverlapJson : String := q
  "{'cpu':{'arch':'x','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'ram','base':'0x0','size':'0x2000','kind':'ram','perms':'rw'},{'name':'al','base':'0x1000','size':'0x1000','kind':'alias','perms':'rw','alias_of':'ram'}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}}}"

-- E14: a device declaring an invalid fidelity combo (observational + full) is rejected.
def badSemJson : String := q
  "{'cpu':{'arch':'x','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'ram','base':'0x0','size':'0x1000','kind':'ram','perms':'rw'}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}},'devices':[{'name':'d','base':'0x40000000','size':'0x10','semantics':{'class':'observational','proof_use':'full'},'schema':{'registers':[{'offset':'0x0','reset':'0x0'}]}}]}"

def faultPolicyFaults : Bool :=
  match loadJson faultJson with
  | .ok m => match (m.busRead 0x9000 32).1 with | .error .unknown => true | _ => false
  | .error _ => false

def negativeTests : List (String × Bool) :=
  [ ("overlap_rejected", isErr (loadJson overlapJson)),
    ("dangling_alias_rejected", isErr (loadJson danglingJson)),
    ("device_shadows_memory_rejected", isErr (loadJson devMemJson)),
    ("window_overlap_rejected", isErr (loadJson windowOverlapJson)),
    ("invalid_endian_rejected", isErr (loadJson invalidEndianJson)),
    ("invalid_policy_rejected", isErr (loadJson invalidPolicyJson)),
    ("invalid_class_rejected", isErr (loadJson invalidClassJson)),
    ("alias_overlap_rejected", isErr (loadJson aliasOverlapJson)),
    ("invalid_fidelity_combo_rejected", isErr (loadJson badSemJson)),
    ("fault_policy_faults", faultPolicyFaults) ]

def main (args : List String) : IO Unit := do
  let mut ok := true
  for path in args do
    let text ← IO.FS.readFile path
    let rt := roundTrips text
    match loadJson text with
    | .error e => IO.println s!"{path}: LOAD FAIL — {e}"; ok := false
    | .ok m =>
      let countsOk := match expectedFor path with
        | some (r, d) => m.regions.size == r && m.devices.size == d
        | none => true
      let good := rt && countsOk && m.busWellFormed
      let tag := if good then "ok" else "FAIL"
      IO.println s!"{path}: regions={m.regions.size} devices={m.devices.size} roundtrip={rt} wellformed={m.busWellFormed} {tag}"
      if !good then ok := false
  for (name, pass) in negativeTests do
    let tag := if pass then "ok" else "FAIL"
    IO.println s!"neg {name}: {tag}"
    if !pass then ok := false
  if !ok then throw (IO.userError "hw ingestion failed")
  IO.println "hw ingestion: PASS"
