module
public import AlgebraicAnalysis.DifferentialOperators.Localization
public import AlgebraicAnalysis.DifferentialOperators.SmoothDerivations
public import AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations

@[expose] public section

/-!
Oracles for the D3 groundwork: uniqueness of differential operators on a
localization, and finiteness and projectivity of `Der_k(A)` for smooth `A`.

* Uniqueness on `ℚ[x, x⁻¹]`: a derivation `D` with `D x = x` agrees with
  `x ∂` on polynomials (Mathlib's `MvPolynomial.derivation_ext`), hence on all
  Laurent polynomials by the library; evaluated at `x⁻¹` it gives `-x⁻¹`, the
  value obtained by hand from `D(x · x⁻¹) = 0`.
* `Der_ℚ(ℚ[x₀, x₁])` is finitely generated and projective by the library; the
  explicit oracle is the decomposition `D = D(x₀) ∂₀ + D(x₁) ∂₁`.
-/

namespace AlgebraicAnalysisTest.DifferentialOperatorsD3

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators MvPolynomial
open AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations

/-- `ℚ[x]`. -/
abbrev P1 := MvPolynomial (Fin 1) ℚ

/-- The powers of `x`. -/
noncomputable abbrev powersX : Submonoid P1 := Submonoid.powers (X 0)

/-- `ℚ[x, x⁻¹]`. -/
abbrev L := Localization.Away (X 0 : P1)

/-- `x` and `x⁻¹` in `ℚ[x, x⁻¹]`. -/
noncomputable abbrev x : L := algebraMap P1 L (X 0)
noncomputable abbrev xInv : L := IsLocalization.Away.invSelf (X 0 : P1)

theorem x_mul_xInv : x * xInv = 1 := IsLocalization.Away.mul_invSelf _

/-- `∂ = d/dx` on `ℚ[x, x⁻¹]`. -/
noncomputable abbrev dx : Derivation ℚ L L := localizedPderiv powersX L 0

/-- Hand computation for any derivation with `D x = x`: `D(x⁻¹) = -x⁻¹`. -/
theorem hand (D : Derivation ℚ L L) (hD : D x = x) : D xInv = -xInv := by
  have h := D.leibniz x xInv
  rw [x_mul_xInv, D.map_one_eq_zero, hD, smul_eq_mul, smul_eq_mul] at h
  calc D xInv = xInv * (x * D xInv) := by rw [← mul_assoc, mul_comm xInv x, x_mul_xInv, one_mul]
    _ = xInv * (-(xInv * x)) := by rw [show x * D xInv = -(xInv * x) by linear_combination -h]
    _ = -xInv := by rw [mul_comm xInv x, x_mul_xInv]; ring

/-- Library: a derivation with `D x = x` is `x ∂`, since both are first-order
operators agreeing on polynomials. -/
theorem eq_x_mul_dx (D : Derivation ℚ L L) (hD : D x = x) :
    D.toLinearMap = multiplication x * dx.toLinearMap := by
  refine eq_of_forall_algebraMap_eq powersX (n := 1) (derivation_mem_order_one D)
    (by simpa using mul_mem_order (multiplication_mem_order_zero x) (derivation_mem_order_one dx))
    fun p => ?_
  have hpoly : D.compAlgebraMap P1 = x • dx.compAlgebraMap P1 := by
    apply MvPolynomial.derivation_ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change D x = x * dx x
    rw [hD, show dx x = 1 by simpa using localizedPderiv_apply_algebraMap_X powersX L 0 0,
      mul_one]
  exact Derivation.congr_fun hpoly p

/-- The library value at `x⁻¹` agrees with the hand computation. -/
example (D : Derivation ℚ L L) (hD : D x = x) :
    (multiplication x * dx.toLinearMap : Module.End ℚ L) xInv = -xInv := by
  rw [← eq_x_mul_dx D hD]
  exact hand D hD

/-! ### Derivations of a smooth algebra -/

/-- `ℚ[x₀, x₁]`. -/
abbrev P2 := MvPolynomial (Fin 2) ℚ

/-- A polynomial ring in finitely many variables is smooth (formally smooth and
of finite presentation, both from Mathlib). -/
instance : Algebra.Smooth ℚ P2 where

example : Module.Finite P2 (Derivation ℚ P2 P2) := finite_derivation_of_smooth ℚ P2
example : Module.Projective P2 (Derivation ℚ P2 P2) := projective_derivation_of_smooth ℚ P2

/-- Explicit oracle: every derivation is `D(x₀) ∂₀ + D(x₁) ∂₁`. -/
example (D : Derivation ℚ P2 P2) : D = D (X 0) • pderiv 0 + D (X 1) • pderiv 1 := by
  apply MvPolynomial.derivation_ext
  intro i
  fin_cases i <;> simp [pderiv_X]

#print axioms eq_of_forall_algebraMap_eq
#print axioms finite_derivation_of_smooth
#print axioms projective_derivation_of_smooth

end AlgebraicAnalysisTest.DifferentialOperatorsD3
