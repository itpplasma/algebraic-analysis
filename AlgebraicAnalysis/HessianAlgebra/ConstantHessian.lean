/- SPDX-License-Identifier: Apache-2.0 -/
-- Modified by itpplasma/algebraic-analysis: package module path changed.

import AlgebraicAnalysis.HessianAlgebra.DerivativeKernel
import AlgebraicAnalysis.HessianAlgebra.AffineInverse

/-! Affine gradients and actual inverses for constant Hessian polynomials. -/

noncomputable section

namespace HessianAlgebra
namespace PolynomialMap

open MvPolynomial

variable {K σ : Type*} [Field K] [CharZero K]
variable [Fintype σ] [DecidableEq σ]

local notation "Poly" => MvPolynomial σ K

theorem gradient_eq_affine_of_hessian_eq_constant
    (f : Poly) (H : Matrix σ σ K)
    (hH : ∀ i j, hessian f i j = C (H i j)) :
    gradient f = affine H (fun i => constantCoeff (gradient f i)) := by
  funext i
  let q : Poly := gradient f i - affine H
    (fun k => constantCoeff (gradient f k)) i
  have hq : ∀ j, pderiv j q = 0 := by
    intro j
    have hlinear : pderiv j (affine H
        (fun k => constantCoeff (gradient f k)) i) = C (H i j) := by
      unfold affine
      rw [map_add, map_sum]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k hk hkj
        simp [pderiv_X_of_ne hkj]
      · simp
    have hderiv : pderiv j (gradient f i) = C (H i j) := by
      change pderiv j (pderiv i f) = C (H i j)
      rw [← hH i j]
      exact partial_comm f j i
    change pderiv j (gradient f i - affine H
      (fun k => constantCoeff (gradient f k)) i) = 0
    rw [map_sub, hderiv, hlinear, sub_self]
  have hqconst := eq_constant_of_pderiv_eq_zero q hq
  have hqcoeff : constantCoeff q = 0 := by
    dsimp [q]
    unfold affine
    rw [map_sub, map_add, map_sum]
    simp [constantCoeff_eq]
  have hqzero : q = 0 := by
    rw [hqconst]
    have hc := congrArg (C : K →+* Poly) hqcoeff
    simpa [constantCoeff_eq] using hc
  exact sub_eq_zero.mp (by simpa [q] using hqzero)

theorem exists_gradientTwoSidedInverse_of_constantHessian
    (f : Poly) (H : Matrix σ σ K)
    (hH : ∀ i j, hessian f i j = C (H i j)) (hdet : H.det ≠ 0) :
    ∃ g, gradientTwoSidedInverse f g := by
  let b := fun i => constantCoeff (gradient f i)
  let g := affineInverse H b
  have ha := affine_twoSidedInverse H b hdet
  have hg := gradient_eq_affine_of_hessian_eq_constant f H hH
  refine ⟨g, ?_⟩
  change TwoSidedInverse (gradient f) (affineInverse H b)
  rw [hg]
  exact ha

end PolynomialMap
end HessianAlgebra

end
