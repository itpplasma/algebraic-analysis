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

example : (atInfinity ℚ (RatFunc.X : ℚ⟮X⟯)).order = -1 := by
  rw [order_atInfinity ℚ _ RatFunc.X_ne_zero]
  simp

example : (atInfinity ℚ ((RatFunc.X : ℚ⟮X⟯)⁻¹)).order = 1 := by
  rw [order_atInfinity ℚ _ (inv_ne_zero RatFunc.X_ne_zero)]
  simp

example : polynomialPart ℚ ((RatFunc.X : ℚ⟮X⟯)⁻¹) = 0 := by
  ext k
  rw [← coeff_atInfinity_eq_polynomialPart]
  rw [map_inv₀, atInfinity_X, HahnSeries.inv_single]
  have hk : -(k : ℤ) ≠ 1 := by omega
  simp [hk]

/-- Removing the polynomial part of `X + X⁻¹` leaves exactly the proper
fraction, whose Laurent order at infinity is one. -/
example :
    (atInfinity ℚ ((RatFunc.X : ℚ⟮X⟯) + RatFunc.X⁻¹) -
      atInfinity ℚ
        (algebraMap ℚ[X] ℚ⟮X⟯
          (polynomialPart ℚ ((RatFunc.X : ℚ⟮X⟯) + RatFunc.X⁻¹)))).orderTop = 1 := by
  have hpart :
      polynomialPart ℚ ((RatFunc.X : ℚ⟮X⟯) + RatFunc.X⁻¹) = Polynomial.X := by
    ext k
    rw [← coeff_atInfinity_eq_polynomialPart, map_add, HahnSeries.coeff_add,
      atInfinity_X, map_inv₀, atInfinity_X, HahnSeries.inv_single]
    by_cases hk : k = 1
    · subst k
      norm_num [HahnSeries.coeff_single]
    · have hneg : -(k : ℤ) ≠ 1 := by omega
      have hfirst : -(k : ℤ) ≠ -1 := by omega
      simp [hfirst, hneg,
        Polynomial.coeff_X_of_ne_one (R := ℚ) hk]
  rw [hpart]
  change
    (atInfinity ℚ ((RatFunc.X : ℚ⟮X⟯) + RatFunc.X⁻¹) -
      atInfinity ℚ (RatFunc.X : ℚ⟮X⟯)).orderTop = 1
  rw [map_add, map_inv₀]
  ring_nf
  rw [atInfinity_X]
  simp [HahnSeries.inv_single]

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
