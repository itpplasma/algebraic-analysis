/- SPDX-License-Identifier: Apache-2.0 -/

import HessianAlgebra.PolynomialMap
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Explicit polynomial inverses for affine linear maps. -/

noncomputable section

namespace HessianAlgebra
namespace PolynomialMap

open MvPolynomial

variable {K : Type*} {σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

local notation "Poly" => MvPolynomial σ K

def affine (A : Matrix σ σ K) (b : σ → K) : σ → Poly :=
  fun i => (∑ j, C (A i j) * X j) + C (b i)

def affineInverse (A : Matrix σ σ K) (b : σ → K) : σ → Poly :=
  fun i => ∑ j, C ((A⁻¹) i j) * (X j - C (b j))

lemma affine_twoSidedInverse (A : Matrix σ σ K) (b : σ → K)
    (hdet : A.det ≠ 0) :
    TwoSidedInverse (affine A b) (affineInverse A b) := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hleft := A.nonsing_inv_mul hunit
  have hright := A.mul_nonsing_inv hunit
  constructor
  · intro i
    simp [substitute, affine, affineInverse]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← map_mul]
    simp_rw [← Finset.sum_mul]
    have hC (j : σ) :
        (∑ x, (C (A i x * (A⁻¹) x j) : Poly)) =
          C (∑ x, A i x * (A⁻¹) x j) := by
      exact (map_sum (C : K →+* Poly) (fun x => A i x * (A⁻¹) x j)
        Finset.univ).symm
    simp_rw [hC]
    have hmatrix (j : σ) :
        (∑ x, A i x * (A⁻¹) x j) = (1 : Matrix σ σ K) i j := by
      simpa [Matrix.mul_apply] using congrFun (congrFun hright i) j
    simp_rw [hmatrix]
    simp [Matrix.one_apply]
  · intro i
    simp [substitute, affine, affineInverse]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← map_mul]
    simp_rw [← Finset.sum_mul]
    have hC (j : σ) :
        (∑ x, (C ((A⁻¹) i x * A x j) : Poly)) =
          C (∑ x, (A⁻¹) i x * A x j) := by
      exact (map_sum (C : K →+* Poly) (fun x => (A⁻¹) i x * A x j)
        Finset.univ).symm
    simp_rw [hC]
    have hmatrix (j : σ) :
        (∑ x, (A⁻¹) i x * A x j) = (1 : Matrix σ σ K) i j := by
      simpa [Matrix.mul_apply] using congrFun (congrFun hleft i) j
    simp_rw [hmatrix]
    simp [Matrix.one_apply]

end PolynomialMap
end HessianAlgebra

end
