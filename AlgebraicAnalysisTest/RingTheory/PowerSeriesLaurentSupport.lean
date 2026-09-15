/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.PowerSeriesLaurentSupport
import Mathlib.Tactic

/-! Concrete threshold and hostile below-threshold oracles. -/

namespace PowerSeries

noncomputable section

private def full : PowerSeries (LaurentSeries ℚ) :=
  PowerSeries.C (HahnSeries.single (-3) 1 + HahnSeries.single 1 1)

private def truncated : PowerSeries (LaurentSeries ℚ) :=
  PowerSeries.C (HahnSeries.single (-3) 1)

private theorem full_lower : LaurentAffineLower 1 (-6) full := by
  intro ell z hz
  by_cases hell : ell = 0
  · subst ell
    by_cases hzneg : z = -3
    · subst z
      omega
    by_cases hzone : z = 1
    · subst z
      omega
    simp [full, hzneg, hzone]
  · rw [show full.coeff ell = 0 by simp [full, PowerSeries.coeff_C, hell]]
    simp

private theorem truncated_lower : LaurentAffineLower 1 (-6) truncated := by
  intro ell z hz
  by_cases hell : ell = 0
  · subst ell
    by_cases hzneg : z = -3
    · subst z
      omega
    · simp [truncated, PowerSeries.coeff_C, hzneg]
  · rw [show truncated.coeff ell = 0 by
      simp [truncated, PowerSeries.coeff_C, hell]]
    simp

private theorem difference_positive :
    LaurentAffineLower 0 2 (full - truncated) := by
  intro ell z hz
  by_cases hell : ell = 0
  · subst ell
    by_cases hzone : z = 1
    · subst z
      omega
    · simp [full, truncated, PowerSeries.coeff_C, hzone]
  · rw [show (full - truncated).coeff ell = 0 by
      simp [full, truncated, PowerSeries.coeff_C, hell]]
    simp

/-- Equality holds at the inclusive threshold `K = 3`. -/
example : ((full ^ 2 - truncated ^ 2).coeff 0).coeff (-3) = 0 := by
  exact LaurentAffineLower.pow_sub_coeff_zero_of_ge 6 2 0 3
    full_lower truncated_lower difference_positive (by omega)

/-- Hostile control: below the threshold, the mixed term survives. -/
example : ((full ^ 2 - truncated ^ 2).coeff 0).coeff (-2) = 2 := by
  simp only [full, truncated, pow_two, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_zero_C]
  change (((HahnSeries.single (-3) 1 + HahnSeries.single 1 1 : LaurentSeries ℚ) *
      (HahnSeries.single (-3) 1 + HahnSeries.single 1 1) -
    HahnSeries.single (-3) 1 * HahnSeries.single (-3) 1).coeff (-2)) = 2
  rw [show ∀ a b : LaurentSeries ℚ,
      (a + b) * (a + b) - a * a = a * b + a * b + b * b by
    intro a b
    ring]
  norm_num [HahnSeries.single_mul_single]

end

end PowerSeries
