/-
L6 (large-use-case plan): a Unicorn-like API surface over the SEI substrate. The
machine is a pure value, so load/read/write/add/remove/snapshot/restore/fork are
value functions; hooks are deterministic queries over the typed event trace; run
goes through the bounded runner; export emits report/trace/frontier artifacts.

C / Rust FFI boundary (specified — not yet built):
  sei_handle sei_load(const char* descriptor_json, const Image* images, size_t n);
  int        sei_mem_read (sei_handle, uint64_t addr, uint32_t width, uint64_t* out);
  int        sei_mem_write(sei_handle, uint64_t addr, uint32_t width, uint64_t val);
  void       sei_add_region(sei_handle, const Region*);
  void       sei_add_device(sei_handle, const Device*);
  void       sei_remove_device(sei_handle, const char* name);
  hook_id    sei_hook_add (sei_handle, hook_kind, callback, void* user);  // code/mem/mmio/exc/irq/stop
  RunReport  sei_run     (sei_handle, uint64_t fuel);
  sei_handle sei_snapshot(sei_handle);  sei_handle sei_fork(sei_handle);
  size_t     sei_export_trace   (sei_handle, char* buf, size_t cap);
  size_t     sei_export_report  (sei_handle, char* buf, size_t cap);
  size_t     sei_export_frontier(sei_handle, char* buf, size_t cap);
The same descriptors used by the Lean tests are accepted here.
-/
import Sei.Core
import Sei.Hw.Descriptor
import Sei.Hw.Runner
import Sei.Hw.Frontier
open Lean Sei.Core Sei.Hw Sei.Hw.Adapter
namespace Sei.Api

def load (descText : String) (images : List (String × ByteArray) := []) : Except String Machine := do
  loadMachine (← parseDescriptor (← Json.parse descText)) images

def memRead (m : Machine) (addr : Nat) (width : Nat := 32) : Except Fault Word × Machine :=
  m.busRead (BitVec.ofNat 32 addr) width
-- writes surface bus faults (cross/perm/unknown) instead of discarding them (#1)
def memWrite (m : Machine) (addr : Nat) (val : Word) (width : Nat := 32) : Except Fault Unit × Machine :=
  m.busWrite (BitVec.ofNat 32 addr) val width

-- add ops preserve bus well-formedness, failing closed on overlap/ambiguity (#2)
def addRegion (m : Machine) (r : Region) : Except String Machine :=
  let m' := { m with regions := m.regions.push r }
  if m'.busWellFormed then .ok m' else .error s!"addRegion {r.name}: breaks bus well-formedness"
def addDevice (m : Machine) (d : Device) : Except String Machine :=
  let m' := { m with devices := m.devices.push d }
  if m'.busWellFormed then .ok m' else .error s!"addDevice {d.name}: breaks bus well-formedness"
def removeDevice (m : Machine) (name : String) : Machine :=
  { m with devices := m.devices.filter (·.name != name) }

-- snapshots are values: restore/fork are O(1) and need no copying
def snapshot (m : Machine) : Machine := m
def restore (snap : Machine) : Machine := snap
def fork (m : Machine) : Machine × Machine := (m, m)

-- hooks are deterministic queries over the trace (every op is already recorded)
def hookEvents (m : Machine) (pred : Effect → Bool) : List Effect := m.effects.toList.filter pred
def codeHook (m : Machine) : List Word :=
  m.effects.toList.filterMap fun e => match e with | .exec pc .. => some pc | _ => none
def mmioHook (m : Machine) : List Word :=
  m.effects.toList.filterMap fun e => match e with
    | .mmioRead _ a .. => some a | .mmioWrite _ a .. => some a | _ => none

/-- #3: every region that declares an `image` must have a matching backing image,
    or the run fails before the first instruction (no silent zero-filled ROM). -/
def requireImages (h : HwEntry) (images : List (String × ByteArray)) : Except String Unit := do
  for r in h.regions do
    match r.image with
    | some name => if ¬ images.any (·.1 == name) then
        throw s!"region {r.name} declares image '{name}' but no matching --image was provided"
    | none => pure ()

/-- Run a descriptor + images under a fuel bound; returns the report and final machine.
    Applies descriptor entry state (sp/vector_base/exception_state/reg_overrides). -/
def run (descText : String) (images : List (String × ByteArray)) (fuel : Nat)
        (traceFull : Bool := true)
    : Except String (RunReport × Machine) := do
  let h ← parseDescriptor (← Json.parse descText)
  requireImages h images
  let m ← loadMachine h images
  let m := if traceFull then m else { m with traceFull := false }
  let e : EntryState := { resetPc := h.resetPc, sp := h.sp, highVectors := h.highVectors,
                          exceptionState := h.exceptionState, regOverrides := h.regOverrides }
  pure (runMachine m h.arch (if h.little then "little" else "big") e "descriptor" fuel)

def exportTrace (m : Machine) : List String := m.effects.toList.map (·.render)
def exportFrontier (m : Machine) : List FrontierTask := frontierTasks m

-- #8: machine-readable report/frontier JSON (not only console text)
def reportJson (rep : RunReport) (m : Machine) : Json :=
  let n (x : Nat) : Json := jnum x 0
  jobj [
    ("arch", jstr rep.arch), ("endian", jstr rep.endian), ("entry", n rep.entry),
    ("sp", n rep.entrySp), ("highVectors", Json.bool rep.highVectors), ("regOverrides", n rep.regOverrides),
    ("regions", n rep.regions), ("devices", n rep.devices), ("fuel", n rep.fuel),
    ("stop", jstr (reprStr rep.stop)), ("lastPc", n rep.lastPc),
    ("events", n rep.events), ("traceHash", n rep.traceHash), ("descriptorId", jstr rep.descriptorId),
    ("unsupported", jarr (rep.unsupported.map fun (pc, op, mn) =>
        jobj [("pc", n pc), ("op", n op), ("mnem", jstr mn)])),
    ("frontiers", jarr ((exportFrontier m).map fun t =>
        jobj [("address", n t.address), ("widths", jarr (t.widths.map n)),
              ("polls", n t.pollCount), ("class", jstr (reprStr t.candidateClass))]))
  ]

end Sei.Api
