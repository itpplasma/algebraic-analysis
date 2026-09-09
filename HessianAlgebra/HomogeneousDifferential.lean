/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Formal partial derivatives preserve the homogeneous grading with degree shift. -/

noncomputable section

namespace HessianAlgebra
namespace PolynomialMap

open MvPolynomial

variable {K : Type*} {σ : Type*} [CommSemiring K]

local notation "Poly" => MvPolynomial σ K

lemma pderiv_homogeneousComponent (i : σ) (n : ℕ) (f : Poly) :
    MvPolynomial.pderiv i (homogeneousComponent (n + 1) f) =
      homogeneousComponent n (MvPolynomial.pderiv i f) := by
  ext m
  rw [coeff_pderiv]
  simp only [coeff_homogeneousComponent]
  rw [coeff_pderiv]
  by_cases h : m.degree = n
  · simp [h, map_add]
  · simp [h, map_add]

lemma pderiv_pderiv_homogeneousComponent (i j : σ) (n : ℕ) (f : Poly) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j
      (homogeneousComponent (n + 2) f)) =
      homogeneousComponent n (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) := by
  rw [pderiv_homogeneousComponent, pderiv_homogeneousComponent]

end PolynomialMap
end HessianAlgebra

end
