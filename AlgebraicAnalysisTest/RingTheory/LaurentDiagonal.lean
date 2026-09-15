/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.LaurentDiagonal
import Mathlib.Tactic

/-! Concrete orientation oracle for the affine diagonal Laurent regrading. -/

namespace LaurentPolynomial

/-- The outer exponent loses the inner exponent; the inner exponent gains the shift. -/
example :
    affineDiagonal (R := ℚ) 2 3
        ((C (T (-4)) : Iterated ℚ) * T 7) =
      (T 9 : Iterated ℚ) * C (T (-1)) := by
  simpa using affineDiagonal_monomial (R := ℚ) 2 3 7 (-4)

/-- Hostile orientation control: the outer exponent is not `ell + q - A`. -/
example :
    affineDiagonal (R := ℚ) 2 3
        ((C (T (-4)) : Iterated ℚ) * T 7) ≠
      (T 1 : Iterated ℚ) * C (T (-1)) := by
  rw [affineDiagonal_monomial]
  intro h
  have h9 := congrArg (fun p : Iterated ℚ => p.coeff 9) h
  norm_num at h9
  have hz : (T (-1) : _root_.LaurentPolynomial ℚ) = 0 := by
    have hc9 :
        (C (T (-1)) * T 9 : Iterated ℚ) =
          .single 9 (T (-1) : _root_.LaurentPolynomial ℚ) :=
      (single_eq_C_mul_T _ _).symm
    have hc1 :
        (C (T (-1)) * T 1 : Iterated ℚ) =
          .single 1 (T (-1) : _root_.LaurentPolynomial ℚ) :=
      (single_eq_C_mul_T _ _).symm
    rw [hc9, hc1] at h9
    rw [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single] at h9
    simpa [Finsupp.single_apply] using h9
  have hm1 := congrArg
    (fun p : _root_.LaurentPolynomial ℚ => p.coeff (-1)) hz
  norm_num [T_apply] at hm1

end LaurentPolynomial
