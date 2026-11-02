module
public import AlgebraicAnalysis.Filtration.GradedSymbol
public import AlgebraicAnalysis.Filtration.SymbolNoetherian
public import AlgebraicAnalysis.Weyl.LeadingSymbol
public import AlgebraicAnalysis.Weyl.AssociatedGraded
public import AlgebraicAnalysis.Weyl.Symbol
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

/-!
# Bernstein symbol of the Weyl algebra

The Bernstein filtration of `A_n(k)` (all phase variables of weight one) has
associated graded ring the polynomial ring `k[x, ∂]` in `2n` variables, graded by
total degree.  This file packages that identification as a
`RingFiltration.GradedSymbol`, which yields:

* right Noetherianity of `A_n(k)`, a second route to the tower argument; and
* `Module.DevLEOmega (A_n(k))ᵐᵒᵖ (A_n(k))`, the deviation bound `Kdim ≤ ω`
  used by Corollary B of the paper.

The degree-`N` symbol is the weighted-degree-`N` component of the normal-form
polynomial, `AlgebraicAnalysis.Weyl.principalComponentOnPiece`.
Its kernel is the strict lower Bernstein piece, which is exactly the
predecessor piece `below N` of the filtration.
-/

namespace AlgebraicAnalysis.Weyl.BernsteinSymbol

open AlgebraicAnalysis AlgebraicAnalysis.Weyl AlgebraicAnalysis.Weyl.Filtration
open AlgebraicAnalysis.Weyl.AssociatedGraded AlgebraicAnalysis.Weyl.LeadingSymbol
open AlgebraicAnalysis.Weyl.PBW

variable (k : Type*) [Field k] (n : ℕ)

/-- The Bernstein filtration of `A_n(k)`: the piece of degree at most `N` is the
span of the normal-ordered words of total degree at most `N`. -/
@[reducible] noncomputable def filtration : RingFiltration k (WeylAlg k n) where
  F N := bernsteinPiece k n N
  mono := fun _ _ h => presentedWeightPiece_mono k (@bernsteinWeight n) h
  one_mem := by
    change (1 : WeylAlg k n) ∈ bernsteinPiece k n 0
    rw [bernsteinPiece, mem_presentedWeightPiece]
    intro m hm
    rw [presentedNormalFormLinearEquiv_one] at hm
    have hm0 : m = 0 := by
      symm
      simpa [MvPolynomial.coeff_one] using hm
    subst m
    simp [monomialWeight]
  mul_le := fun i j => Submodule.mul_le.mpr fun _ hx _ hy =>
    mul_mem_bernsteinPiece k hx hy
  exhaustive := by
    apply eq_top_iff.mpr
    intro a _
    obtain ⟨N, hN⟩ := exists_mem_bernsteinPiece k a
    exact Submodule.mem_iSup_of_mem N hN

/-- The Bernstein grading of the polynomial symbol ring: homogeneous pieces of
total degree `N`. -/
abbrev grading : ℕ → Submodule k (SymbolRing k n) :=
  fun N => MvPolynomial.weightedHomogeneousSubmodule k (@bernsteinWeight n) N

/-- The degree-`N` symbol vanishes exactly on the strict lower Bernstein piece. -/
theorem principal_eq_zero_iff (N : ℕ)
    (x : presentedWeightPiece k (@bernsteinWeight n) N) :
    principalComponentOnPiece k (@bernsteinWeight n) N x = 0 ↔
      (x : WeylAlg k n) ∈ presentedStrictLowerPiece k (@bernsteinWeight n) N := by
  rw [← LinearMap.mem_ker, mem_ker_principalComponentOnPiece_iff]

/-- The Bernstein principal symbol as a `RingFiltration.GradedSymbol`. -/
noncomputable def symbol : RingFiltration.GradedSymbol (filtration k n) (grading k n) where
  gr N := principalComponentOnPiece k (@bernsteinWeight n) N
  gr_surjective N := principalComponentOnPiece_surjective k (@bernsteinWeight n)
  gr_eq_zero_iff N x :=
    (principal_eq_zero_iff k n N x).trans (by cases N <;> exact Iff.rfl)
  gr_mul i j x y := by
    exact presentedPrincipalComponent_mul_bernstein k x.2 y.2

/-- The Bernstein symbol algebra has finite Krull dimension. -/
theorem ringKrullDim_symbolRing_ne_top :
    ringKrullDim (SymbolRing k n) ≠ ⊤ := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, Nat.card_sum, Nat.card_fin]
  intro h
  exact ENat.natCast_ne_top (n + n) (Option.some_injective _ h)

/-- Right Noetherianity of `A_n(k)` from the Bernstein symbol. -/
theorem isNoetherian_right :
    IsNoetherian (WeylAlg k n)ᵐᵒᵖ (WeylAlg k n) :=
  letI := MvPolynomial.weightedGradedAlgebra k (@bernsteinWeight n)
  (symbol k n).isNoetherian_right

/-- Deviation at most `ω` on the right ideals of `A_n(k)`, from the Bernstein
symbol and the finite Krull dimension of the symbol ring. -/
theorem devLEOmega_right :
    Module.DevLEOmega (WeylAlg k n)ᵐᵒᵖ (WeylAlg k n) :=
  letI := MvPolynomial.weightedGradedAlgebra k (@bernsteinWeight n)
  (symbol k n).devLEOmega_right (ringKrullDim_symbolRing_ne_top k n)

end AlgebraicAnalysis.Weyl.BernsteinSymbol
