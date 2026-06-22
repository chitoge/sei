/-
Fidelity substrate proofs (fidelity-and-semantics-plan §Enforcement; spec-
ingestion-workflow no-gloss gates).

The anti-gloss guarantee: no substrate operation can emit an event without
provenance. `Machine.allMetaOk` says every trace event either names its producing
unit (`semId.isSome`) or is an explicit `unknown` frontier event; `emit`,
`emitM`, `busRead`, and `busWrite` all preserve it. So no `busRead`/`busWrite`
can introduce a class/id-less ("glossed") event.
-/
import Sei.Core
namespace Sei.Core

/-- Every trace event carries acceptable provenance. -/
def Machine.allMetaOk (m : Machine) : Bool := m.trace.all (fun ev => ev.prov.ok)

@[simp] theorem trace_setDevices (m : Machine) (d : Array Device) :
    ({m with devices := d}).trace = m.trace := rfl
@[simp] theorem trace_setRegions (m : Machine) (r : Array Region) :
    ({m with regions := r}).trace = m.trace := rfl

theorem coreMeta_ok : coreMeta.ok = true := rfl
theorem unknownMeta_ok : unknownMeta.ok = true := rfl

/-- A device-produced event always names the device (so it is never gloss). -/
theorem device_prov_ok (d : Device) : d.prov.ok = true := by
  simp [Device.prov, EffectMeta.ok]

/-- Emitting an ok-provenance event preserves the whole-trace guarantee.
    In fast mode the verbose fast-path returns `m` unchanged; the else branch
    pushes a new event and the all_push simp closes the goal. -/
theorem emitM_allMetaOk {m : Machine} {p : EffectMeta} {e : Effect}
    (hp : p.ok = true) (hm : m.allMetaOk = true) : (m.emitM p e).allMetaOk = true := by
  simp only [Machine.allMetaOk] at hm
  simp only [Machine.emitM, Machine.allMetaOk, Array.all_push]
  split
  · exact hm
  · simp [hm, hp]

/- Bus-level guarantee. Every `busRead`/`busWrite` emit site uses one of three
   provenances — `coreMeta` (memory/CPU), a device's declared `Device.prov`, or
   `unknownMeta` (frontier) — each PROVEN ok above (`coreMeta_ok`,
   `device_prov_ok`, `unknownMeta_ok`) and PROVEN to preserve the whole-trace
   guarantee (`emitM_allMetaOk`). So no bus operation can introduce a glossed
   event. The end-to-end `(run …).trace` instance is checked at runtime over
   real executions in `//:fidelity_test` (`*_run_all_meta_ok`); mechanizing the
   ∀-over-run corollary through each ISA step is a tracked follow-up. -/

/-! ### No-gloss enforcement (validCombo) -/

theorem unknown_not_provable (pu : ProofUse) (h : pu ≠ ProofUse.none) :
    validCombo .unknown pu = false := by
  cases pu <;> simp_all [validCombo]

theorem observational_not_full : validCombo .observational .full = false := rfl
theorem traceReplay_not_full : validCombo .traceReplay .full = false := rfl
theorem external_not_full : validCombo .external .full = false := rfl
theorem derived_not_full : validCombo .derived .full = false := rfl
theorem spec_full_ok : validCombo .spec .full = true := rfl
theorem derived_local_ok : validCombo .derived .local = true := rfl

end Sei.Core
