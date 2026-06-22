/-
L7 (large-use-case plan): promotion & regression discipline. A promoted CPU/
device/import artifact must carry source intake, classification, fidelity
metadata, a validation record, and an unsupported-feature inventory; and a model
classified observational/traceReplay/external/unknown cannot be promoted as
`proof_use: full` (enforced by the core `validCombo`). Semantic hashes are stable
and used in regression reports.
-/
import Sei.Core
namespace Sei.Hw
open Sei.Core

structure PromotionRecord where
  id : String
  source : String                 -- where the artifact came from (intake)
  cls : SemClass                  -- classification
  proofUse : ProofUse
  validation : String             -- what it advances / what it does not prove
  unsupported : List String       -- unsupported-feature inventory
  semanticHash : Nat
  deriving Repr, DecidableEq

/-- A stable, content-addressed hash for regression reports. -/
def semanticHash (s : String) : Nat :=
  s.toList.foldl (fun h c => (h * 1000003 + c.toNat + 1) % 2147483647) 7

def PromotionRecord.meta (r : PromotionRecord) : SemanticsMeta :=
  { id := r.id, cls := r.cls, proofUse := r.proofUse, source := r.source }

/-- The promotion gate: required fields present and a sound class/proof_use combo. -/
def promotable (r : PromotionRecord) : Except String Unit := do
  if r.source.isEmpty then throw s!"{r.id}: missing source intake"
  if r.validation.isEmpty then throw s!"{r.id}: missing validation record"
  if ¬ r.meta.valid then
    throw s!"{r.id}: a non-spec model cannot be promoted as proof_use: full"
  pure ()

end Sei.Hw
