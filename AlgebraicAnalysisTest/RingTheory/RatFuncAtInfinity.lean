/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.RatFuncAtInfinity
import Mathlib.Tactic

/-! Concrete orientation and proper-fraction oracles for rational expansion at infinity. -/

open Polynomial

namespace RatFunc

example :
    (atInfinity ℚ (RatFunc.X : ℚ⟮X⟯)).coeff (-1) = 1 := by
  rw [atInfinity_X]
  simp

/-- Hostile orientation control: `X` contributes at exponent `-1`, not `+1`. -/
example :
    (atInfinity ℚ (RatFunc.X : ℚ⟮X⟯)).coeff 1 = 0 := by
  rw [atInfinity_X]
  simp

/-- A proper fraction starts in strictly positive Laurent degree at infinity. -/
example :
    (atInfinity ℚ ((RatFunc.X : ℚ⟮X⟯)⁻¹)).coeff 0 = 0 := by
  rw [map_inv₀, atInfinity_X, HahnSeries.inv_single]
  norm_num [HahnSeries.coeff_single]

example : polynomialPart ℚ ((RatFunc.X : ℚ⟮X⟯)⁻¹) = 0 := by
  ext k
  rw [← coeff_atInfinity_eq_polynomialPart]
  rw [map_inv₀, atInfinity_X, HahnSeries.inv_single]
  have hk : -(k : ℤ) ≠ 1 := by omega
  simp [hk]

example :
    (atInfinity ℚ
      (algebraMap ℚ[X] ℚ⟮X⟯
        ((Polynomial.X : ℚ[X]) ^ 2 + Polynomial.C 3 * Polynomial.X +
          Polynomial.C 2))).coeff (-(2 : ℤ)) = 1 := by
  convert
    (coeff_atInfinity_algebraMap (K := ℚ)
      ((Polynomial.X : ℚ[X]) ^ 2 + Polynomial.C 3 * Polynomial.X +
        Polynomial.C 2) 2) using 1 <;> norm_num

end RatFunc
