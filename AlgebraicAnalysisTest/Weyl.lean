module
public import AlgebraicAnalysis.Weyl.Simplicity
public import AlgebraicAnalysis.Weyl.BernsteinSymbol
public import AlgebraicAnalysis.Weyl.Domain
public import Mathlib.Algebra.Field.ZMod

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
* Domain: `∂ ≠ 0` and `x ≠ 0` follow from `∂ x - x ∂ = 1` alone, so the domain
  instance gives `∂ x ≠ 0` and left cancellation by `∂`; over `ZMod 2`, where
  simplicity fails, `A_1` is still a domain.
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

/-- `∂ ≠ 0` in `A_1(ℚ)`, from the commutator relation only. -/
theorem momentum_ne_zero : generator ℚ 1 (.inr 0) ≠ 0 := by
  intro h
  have h1 := momentum_mul_coordinate_sub_coordinate_mul
  rw [h, zero_mul, mul_zero, sub_zero] at h1
  exact zero_ne_one h1

/-- `x ≠ 0` in `A_1(ℚ)`, from the commutator relation only. -/
theorem coordinate_ne_zero : generator ℚ 1 (.inl 0) ≠ 0 := by
  intro h
  have h1 := momentum_mul_coordinate_sub_coordinate_mul
  rw [h, zero_mul, mul_zero, sub_zero] at h1
  exact zero_ne_one h1

/-- The product `∂ x` of `A_1(ℚ)` is nonzero. -/
theorem momentum_mul_coordinate_ne_zero :
    generator ℚ 1 (.inr 0) * generator ℚ 1 (.inl 0) ≠ 0 :=
  mul_ne_zero momentum_ne_zero coordinate_ne_zero

/-- A nonzero product of higher degree: `∂² x³ (x + ∂) ≠ 0` in `A_1(ℚ)`. -/
example : generator ℚ 1 (.inr 0) ^ 2 * generator ℚ 1 (.inl 0) ^ 3 *
    (generator ℚ 1 (.inl 0) + generator ℚ 1 (.inr 0)) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ momentum_ne_zero)
    (pow_ne_zero _ coordinate_ne_zero)) ?_
  intro h
  have h1 : generator ℚ 1 (.inr 0) * (generator ℚ 1 (.inl 0) + generator ℚ 1 (.inr 0)) -
      (generator ℚ 1 (.inl 0) + generator ℚ 1 (.inr 0)) * generator ℚ 1 (.inr 0) = 1 := by
    rw [mul_add, add_mul, add_sub_add_right_eq_sub]
    exact momentum_mul_coordinate_sub_coordinate_mul
  rw [h, mul_zero, zero_mul, sub_zero] at h1
  exact zero_ne_one h1

/-- Left cancellation by `∂` in `A_1(ℚ)`. -/
example (b c : WeylAlg ℚ 1) (h : generator ℚ 1 (.inr 0) * b = generator ℚ 1 (.inr 0) * c) :
    b = c :=
  mul_left_cancel₀ momentum_ne_zero h

/-- `A_1(𝔽₂)` is a domain, although it is not simple (`x²` is central). -/
example : IsDomain (WeylAlg (ZMod 2) 1) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  inferInstance

/-- The domain statement in the form of the task. -/
example : NoZeroDivisors (WeylAlg ℚ 2) := noZeroDivisors ℚ 2

#print axioms momentum_mul_coordinate_sub_coordinate_mul
#print axioms ringKrullDim_symbolRing_one
#print axioms Simplicity.isSimpleRing_weylAlg
#print axioms momentum_mul_coordinate_ne_zero
#print axioms AlgebraicAnalysis.Weyl.noZeroDivisors
#print axioms AlgebraicAnalysis.Weyl.isDomain
#print axioms AlgebraicAnalysis.RingFiltration.GradedSymbol.isDomain

end AlgebraicAnalysisTest.Weyl
