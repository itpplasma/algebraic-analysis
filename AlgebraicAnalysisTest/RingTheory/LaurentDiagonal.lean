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

/-- Powers multiply both affine shifts and preserve the concrete orientation. -/
example :
    (affineDiagonal (R := ℚ) 2 3
        ((C (T (-4)) : Iterated ℚ) * T 7)) ^ 2 =
      (T 18 : Iterated ℚ) * C (T (-2)) := by
  rw [affineDiagonal_monomial, mul_pow, T_pow, ← map_pow C, T_pow]
  norm_num

/-- API oracle for the shift-scaling power law. -/
example :
    (affineDiagonal (R := ℚ) 2 3
        ((C (T (-4)) : Iterated ℚ) * T 7)) ^ 2 =
      affineDiagonal 4 6
        (((C (T (-4)) : Iterated ℚ) * T 7) ^ 2) := by
  exact affineDiagonal_pow 2 3 _ 2

/-- A concrete coefficient is recovered at the inverse affine index. -/
example :
    ((affineDiagonal (R := ℚ) 2 3
        ((C (T (-4)) : Iterated ℚ) * T 7)).coeff 9).coeff
          (-1) = 1 := by
  rw [affineDiagonal_coeff]
  have hmono :
      (C (T (-4)) * T 7 : Iterated ℚ) =
        .single 7 (T (-4) : _root_.LaurentPolynomial ℚ) :=
    (single_eq_C_mul_T _ _).symm
  rw [hmono, AddMonoidAlgebra.coeff_single]
  norm_num [Finsupp.single_apply, T_apply]

/-- Hostile coefficient control: the same inner degree at the wrong outer
degree vanishes. -/
example :
    ((affineDiagonal (R := ℚ) 2 3
        ((C (T (-4)) : Iterated ℚ) * T 7)).coeff 8).coeff
          (-1) = 0 := by
  rw [affineDiagonal_coeff]
  have hmono :
      (C (T (-4)) * T 7 : Iterated ℚ) =
        .single 7 (T (-4) : _root_.LaurentPolynomial ℚ) :=
    (single_eq_C_mul_T _ _).symm
  rw [hmono, AddMonoidAlgebra.coeff_single]
  norm_num [Finsupp.single_apply]

end LaurentPolynomial
