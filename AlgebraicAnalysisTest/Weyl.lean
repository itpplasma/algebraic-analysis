module
public import AlgebraicAnalysis.Weyl.Simplicity
public import AlgebraicAnalysis.Weyl.BernsteinSymbol

@[expose] public section

/-!
Oracles for the Weyl algebra core.

* Sign convention: in `A_1(ℚ)` the generators satisfy `∂ x - x ∂ = 1`, computed
  from the entries of the standard symplectic matrix `Matrix.J`, which is
  independent of the presentation's bookkeeping.
* Bernstein symbol: the symbol algebra of `A_n(k)` is a polynomial ring in
  `2n` variables, so its Krull dimension is `2n` (Mathlib's count of the
  variables of `MvPolynomial`).
* Simplicity: a two-sided ideal of `A_1(ℚ)` containing the nonzero element
  `∂` is the whole algebra, the consequence of simplicity used downstream.
-/

namespace AlgebraicAnalysisTest.Weyl

open AlgebraicAnalysis.Weyl

/-- The momentum `∂ = generator (inr 0)` and coordinate `x = generator (inl 0)`
of `A_1(ℚ)` satisfy `∂ x - x ∂ = 1`. -/
theorem momentum_mul_coordinate_sub_coordinate_mul :
    generator ℚ 1 (.inr 0) * generator ℚ 1 (.inl 0) -
      generator ℚ 1 (.inl 0) * generator ℚ 1 (.inr 0) = 1 := by
  have h := freeWeylGenerator_commutator (Matrix.J (Fin 1) ℚ) (.inr 0) (.inl 0)
  have hJ : Matrix.J (Fin 1) ℚ (.inr 0) (.inl 0) = 1 := by
    simp [Matrix.J]
  rw [hJ, map_one] at h
  exact h

/-- The symbol algebra of `A_n(k)` has Krull dimension `2n`. -/
theorem ringKrullDim_symbolRing_one :
    ringKrullDim (MvPolynomial (PhaseVar 1) ℚ) = 2 := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, Nat.card_sum, Nat.card_fin]
  norm_num

/-- The Bernstein symbol gives the deviation bound on the right ideals of `A_1(ℚ)`. -/
example : Module.DevLEOmega (WeylAlg ℚ 1)ᵐᵒᵖ (WeylAlg ℚ 1) :=
  BernsteinSymbol.devLEOmega_right ℚ 1

/-- Simplicity of `A_1(ℚ)`, in the form used downstream. -/
example : IsSimpleRing (WeylAlg ℚ 1) := Simplicity.isSimpleRing_weylAlg ℚ 1

/-- Behavioural consequence of simplicity: a two-sided ideal of `A_1(ℚ)` that
contains the momentum `∂` contains `1`. -/
example (I : TwoSidedIdeal (WeylAlg ℚ 1))
    (hI : generator ℚ 1 (.inr 0) ∈ I) : (1 : WeylAlg ℚ 1) ∈ I := by
  haveI : IsSimpleRing (WeylAlg ℚ 1) := Simplicity.isSimpleRing_weylAlg ℚ 1
  refine IsSimpleRing.one_mem_of_ne_zero_mem I (x := generator ℚ 1 (.inr 0)) ?_ hI
  intro h
  have h1 := momentum_mul_coordinate_sub_coordinate_mul
  rw [h, zero_mul, mul_zero, sub_zero] at h1
  exact zero_ne_one h1

#print axioms momentum_mul_coordinate_sub_coordinate_mul
#print axioms ringKrullDim_symbolRing_one
#print axioms Simplicity.isSimpleRing_weylAlg

end AlgebraicAnalysisTest.Weyl
