import Mathlib.Algebra.Ring.Rat
import AlgebraicAnalysis.RingTheory.TwoGeneratorIdentity

/-! Concrete and abstract consumers of unit-denominator transport. -/

open AlgebraicAnalysis

example : TwoGeneratorIdentity ℚ := by
  intro d hd
  refine ⟨0, d⁻¹, 0, ?_⟩
  rw [zero_mul, mul_zero, add_zero]
  exact (mul_inv_cancel₀ hd).symm

example {R : Type*} [Ring R] (hR : TwoGeneratorIdentity R) :
    TwoGeneratorIdentity R := by
  apply TwoGeneratorIdentity.of_rightUnitClearing (f := RingHom.id R) hR
  intro q hq
  exact ⟨q, 1, isUnit_one, by simp⟩

example {R : Type*} [Ring R] (hR : TwoGeneratorIdentity R) :
    TwoGeneratorIdentity R := by
  apply TwoGeneratorIdentity.of_leftUnitClearing (f := RingHom.id R) hR
  intro q hq
  exact ⟨q, 1, isUnit_one, by simp⟩

example {R : Type*} {L : Type*} [Ring R] [Ring L]
    (f : R →+* L) (hR : TwoGeneratorIdentity R)
    (hclear : ∀ q : L, q ≠ 0 →
      ∃ a s : R, IsUnit (f s) ∧ q * f s = f a) :
    TwoGeneratorIdentity L :=
  TwoGeneratorIdentity.of_rightUnitClearing (f := f) hR hclear

example {R : Type*} {L : Type*} [Ring R] [Ring L]
    (f : R →+* L) (hR : TwoGeneratorIdentity R)
    (hclear : ∀ q : L, q ≠ 0 →
      ∃ a : R, ∃ u : L, IsUnit u ∧ u * q = f a) :
    TwoGeneratorIdentity L :=
  TwoGeneratorIdentity.of_leftUnitClearing (f := f) hR hclear

#print axioms AlgebraicAnalysis.TwoGeneratorIdentity.of_rightUnitClearing
#print axioms AlgebraicAnalysis.TwoGeneratorIdentity.of_leftUnitClearing
