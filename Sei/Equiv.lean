/-
Block-translation equivalence (E10 target 4).

Two independently-written executors of the same toy basic block must compute the
same result. The "native" executor commutes/reassociates its arithmetic (as a
real code generator might) but is proven equal to the reference for all inputs.

Block:  r2 := r0 + r1 ;  r4 := r2 + 5
-/
namespace Sei.Equiv

/-- Reference executor: straightforward left-to-right evaluation. -/
def refBlock (r0 r1 : Nat) : Nat × Nat :=
  let r2 := r0 + r1
  let r4 := r2 + 5
  (r2, r4)

/-- "Native" executor: same block with commuted operands (a legal codegen). -/
def natBlock (r0 r1 : Nat) : Nat × Nat :=
  let r2 := r1 + r0
  let r4 := 5 + r2
  (r2, r4)

/-- The two executors agree on every input state. -/
theorem block_equiv (r0 r1 : Nat) : refBlock r0 r1 = natBlock r0 r1 := by
  simp only [refBlock, natBlock, Prod.mk.injEq]
  omega

/-- A single-step ADD equivalence (wrapped to 32 bits) used by the toy ISA. -/
def refAdd (a b : Nat) : Nat := (a + b) % 4294967296
def natAdd (a b : Nat) : Nat := (b + a) % 4294967296

theorem add_equiv (a b : Nat) : refAdd a b = natAdd a b := by
  simp only [refAdd, natAdd]
  omega

end Sei.Equiv
