/- SPDX-License-Identifier: Apache-2.0 -/

import HessianAlgebra.HomogeneousSubstitution

/-! Degree support bounds under homogeneous substitution. -/

noncomputable section

namespace HessianAlgebra

open MvPolynomial
open PolynomialMap

variable {K : Type*} {σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- Any predicate on exponent degree that holds on the source support is
preserved by substitution by degree-one homogeneous polynomials. -/
theorem support_degree_predicate_substitute (g : σ → MvPolynomial σ K)
    (hg : ∀ i, (g i).IsHomogeneous 1) (H : MvPolynomial σ K)
    (Q : ℕ → Prop) (hQ : ∀ e, coeff e H ≠ 0 → Q e.degree) :
    ∀ e, coeff e (PolynomialMap.substitute g H) ≠ 0 → Q e.degree := by
  intro e he
  by_contra hnot
  have hz : homogeneousComponent e.degree H = 0 := by
    apply homogeneousComponent_eq_zero'
    intro f hf hdeg
    exact hnot (hdeg ▸ hQ f (mem_support_iff.mp hf))
  have hz' := congrArg (coeff e) (homogeneousComponent_substitute g hg e.degree H)
  rw [hz, (PolynomialMap.substitute g).map_zero] at hz'
  exact he (by simpa [coeff_homogeneousComponent] using hz')

/-- Substitution by degree-one homogeneous polynomials preserves an upper
degree bound on the support. -/
theorem support_degree_le_substitute (g : σ → MvPolynomial σ K)
    (hg : ∀ i, (g i).IsHomogeneous 1) (H : MvPolynomial σ K) (D : ℕ)
    (hH : ∀ e ∈ H.support, e.degree ≤ D) :
    ∀ e ∈ (PolynomialMap.substitute g H).support, e.degree ≤ D := by
  intro e he
  exact support_degree_predicate_substitute g hg H (fun n => n ≤ D) (by
    intro f hf
    exact hH f (mem_support_iff.mpr hf)) e (mem_support_iff.mp he)

/-- Substitution by degree-one homogeneous polynomials preserves a lower
degree bound on the support. -/
theorem support_degree_ge_substitute (g : σ → MvPolynomial σ K)
    (hg : ∀ i, (g i).IsHomogeneous 1) (H : MvPolynomial σ K) (D : ℕ)
    (hH : ∀ e ∈ H.support, D ≤ e.degree) :
    ∀ e ∈ (PolynomialMap.substitute g H).support, D ≤ e.degree := by
  intro e he
  exact support_degree_predicate_substitute g hg H (fun n => D ≤ n) (by
    intro f hf
    exact hH f (mem_support_iff.mpr hf)) e (mem_support_iff.mp he)

end HessianAlgebra
