/-
Bus decode determinism and non-overlap (E10 target 2).

A bus address decodes to a region. If regions are pairwise non-overlapping, no
address decodes to two regions (decode is unambiguous), and a pure `resolve`
function is deterministic by construction.
-/
namespace Sei.Bus

structure Region where
  base : Nat
  size : Nat

/-- An address lies in a region's half-open window `[base, base+size)`. -/
def contains (r : Region) (a : Nat) : Prop := r.base ≤ a ∧ a < r.base + r.size

/-- Two regions are disjoint if their windows do not overlap. -/
def Disjoint (r₁ r₂ : Region) : Prop :=
  r₁.base + r₁.size ≤ r₂.base ∨ r₂.base + r₂.size ≤ r₁.base

/-- Non-overlap ⇒ no address resolves to two regions. -/
theorem no_double_decode (r₁ r₂ : Region) (a : Nat)
    (h : Disjoint r₁ r₂) : ¬ (contains r₁ a ∧ contains r₂ a) := by
  rcases h with h | h <;>
  · rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩
    omega

/-- First-match decode over a region list (a pure function, hence deterministic
    by construction; the substantive properties are the two theorems below). -/
def resolve : List Region → Nat → Option Nat
  | [], _ => none
  | r :: rs, a => if r.base ≤ a ∧ a < r.base + r.size then some r.base else resolve rs a

/-- If the first region matches, that is the decoded region (no later region can
    shadow it) — first-match decode is well-defined. -/
theorem resolve_first_match (r : Region) (rs : List Region) (a : Nat)
    (h : r.base ≤ a ∧ a < r.base + r.size) :
    resolve (r :: rs) a = some r.base := by
  simp [resolve, h.1, h.2]

/-- If the head region does not contain the address, decode falls through to the
    rest of the list (the recursion is exactly first-match). -/
theorem resolve_skip (r : Region) (rs : List Region) (a : Nat)
    (h : ¬ (r.base ≤ a ∧ a < r.base + r.size)) :
    resolve (r :: rs) a = resolve rs a := by
  simp [resolve, h]

end Sei.Bus
