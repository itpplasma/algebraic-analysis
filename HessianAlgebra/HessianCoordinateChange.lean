/- SPDX-License-Identifier: Apache-2.0 -/

import HessianAlgebra.CoordinateChange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Hessian and Hessian-determinant identities under linear substitution. -/

noncomputable section

namespace HessianAlgebra
namespace PolynomialMap

open MvPolynomial

variable {K : Type*} {σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

local notation "Poly" => MvPolynomial σ K

/-- The matrix view of the existing polynomial-map Hessian. -/
def hessianMatrix (f : Poly) : Matrix σ σ Poly := hessian f

/-- The Hessian transforms by congruence under an arbitrary linear
substitution. No invertibility hypothesis on the matrix is needed. -/
theorem hessian_linear_pullback (f : Poly) (T : Matrix σ σ K) :
    hessianMatrix (substitute (linear T) f) =
      T.transpose.map C *
        (hessianMatrix f).map (substitute (linear T)) *
      T.map C := by
  apply Matrix.ext
  intro i j
  have hgrad := congrFun (gradient_linear_pullback f T) j
  have hsecond := congrArg (partialDerivative i) hgrad
  change partialDerivative i (gradient (substitute (linear T) f) j) = _
  rw [hsecond]
  simp only [partialDerivative, map_sum, pderiv_mul, pderiv_C, mul_zero,
    add_zero]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    hessianMatrix]
  apply Finset.sum_congr rfl
  intro k hk
  have hkchain := pderiv_substitute (partialDerivative k f) (linear T) i
  change pderiv i (substitute (linear T) (pderiv k f)) = _ at hkchain
  rw [hkchain]
  apply congrArg (fun q : Poly => q * C (T k j))
  apply Finset.sum_congr rfl
  intro l hl
  rw [partial_linear]
  change substitute (linear T) (partialDerivative l (partialDerivative k f)) *
      C (T l i) =
    C (T l i) *
      substitute (linear T) (partialDerivative l (partialDerivative k f))
  ring

/-- The Hessian determinant acquires the square of the determinant of the
linear substitution matrix. -/
theorem det_hessian_linear_pullback (f : Poly) (T : Matrix σ σ K) :
    Matrix.det (hessianMatrix (substitute (linear T) f)) =
      C (T.det ^ 2) *
        substitute (linear T) (Matrix.det (hessianMatrix f)) := by
  rw [hessian_linear_pullback, Matrix.det_mul, Matrix.det_mul]
  have hleft : (T.transpose.map (C : K → Poly)).det =
      (C : K → Poly) T.det := by
    rw [← RingHom.mapMatrix_apply]
    rw [← (C : K →+* Poly).map_det T.transpose, Matrix.det_transpose]
  have hmiddle : ((hessianMatrix f).map (substitute (linear T))).det =
      substitute (linear T) (hessianMatrix f).det := by
    rw [← RingHom.mapMatrix_apply]
    exact ((substitute (linear T)).map_det (hessianMatrix f)).symm
  have hright : (T.map (C : K → Poly)).det = (C : K → Poly) T.det := by
    rw [← RingHom.mapMatrix_apply]
    exact ((C : K →+* Poly).map_det T).symm
  rw [hleft, hmiddle, hright]
  simp only [map_pow]
  ring

end PolynomialMap
end HessianAlgebra

end
