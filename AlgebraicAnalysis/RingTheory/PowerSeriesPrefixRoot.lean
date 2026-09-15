/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Finite coefficient uniqueness for power-series roots

Matching coefficients of two nonzero-normalized powers through a finite
order forces the same finite coefficient prefix for their roots.
-/

open scoped PowerSeries

namespace PowerSeries

variable {R : Type*}

/-- Agreement of power-series coefficients through a fixed degree is preserved
at that degree by every natural-number power. -/
theorem coeff_pow_eq_of_coeff_eq_of_le
    [CommSemiring R] (f g : R⟦X⟧) (d n : ℕ)
    (hcoeff : ∀ i, i ≤ n → coeff i f = coeff i g) :
    coeff n (f ^ d) = coeff n (g ^ d) := by
  induction d generalizing n with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hadd : p.1 + p.2 = n :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [ih p.1 (fun i hi ↦ hcoeff i (hi.trans (by omega))),
        hcoeff p.2 (by omega)]

private lemma coeff_mul_eq_of_left_coeff_eq_zero_below
    [CommSemiring R] {i : ℕ} {u v : R⟦X⟧}
    (hu : ∀ j, j < i → coeff j u = 0) :
    coeff i (u * v) = coeff i u * constantCoeff v := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  rw [Finset.sum_eq_zero]
  · simp [coeff_zero_eq_constantCoeff_apply]
  intro j hj
  exact mul_eq_zero_of_left (hu j (Finset.mem_range.mp hj)) _

private lemma sub_pow_eq_sub_mul_geom_sum
    [CommRing R] {n : ℕ} (f g : R⟦X⟧) :
    f ^ n - g ^ n =
      (f - g) * ∑ j ∈ Finset.range n, f ^ j * g ^ (n - 1 - j) := by
  simpa [mul_comm] using (geom_sum₂_mul f g n).symm

/-- If two power-series powers agree through degree `K`, and their roots have
the same nonzero constant coefficient, then the roots agree through degree
`K`. Characteristic zero is needed to cancel the power exponent. -/
theorem coeff_eq_of_pow_coeff_eq_of_le
    [CommRing R] [NoZeroDivisors R] [CharZero R]
    {K n : ℕ} (hn : n ≠ 0) {f g : R⟦X⟧}
    (hzero : coeff 0 f = coeff 0 g) (hfzero : coeff 0 f ≠ 0)
    (hpow : ∀ i ≤ K, coeff i (f ^ n) = coeff i (g ^ n)) :
    ∀ i ≤ K, coeff i f = coeff i g := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hizero : i = 0
    · simpa [hizero] using hzero
    · have hdiff : ∀ j, j < i → coeff j (f - g) = 0 := by
        intro j hj
        change coeff j f - coeff j g = 0
        exact sub_eq_zero.mpr (ih j hj (by omega))
      have hpcoeff : coeff i (f ^ n - g ^ n) = 0 := by
        change coeff i (f ^ n) - coeff i (g ^ n) = 0
        simp [hpow i hi]
      rw [sub_pow_eq_sub_mul_geom_sum] at hpcoeff
      rw [coeff_mul_eq_of_left_coeff_eq_zero_below hdiff] at hpcoeff
      have hsum :
          constantCoeff
              (∑ j ∈ Finset.range n, f ^ j * g ^ (n - 1 - j)) =
            (n : R) * (coeff 0 f) ^ (n - 1) := by
        rw [map_sum]
        calc
          (∑ j ∈ Finset.range n,
              constantCoeff (f ^ j * g ^ (n - 1 - j))) =
              ∑ j ∈ Finset.range n,
                (coeff 0 f) ^ j * (coeff 0 g) ^ (n - 1 - j) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [map_mul, map_pow, coeff_zero_eq_constantCoeff_apply]
          _ = ∑ _j ∈ Finset.range n, (coeff 0 f) ^ (n - 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← hzero, ← pow_add]
            congr 1
            exact Nat.add_sub_of_le
              (Nat.le_sub_one_of_lt (Finset.mem_range.mp hj))
          _ = (n : R) * (coeff 0 f) ^ (n - 1) := by
            simp [nsmul_eq_mul]
      rw [hsum] at hpcoeff
      have hdiffi : coeff i (f - g) = 0 :=
        (mul_eq_zero.mp hpcoeff).resolve_right <| by
          exact mul_ne_zero (Nat.cast_ne_zero.mpr hn)
            (pow_ne_zero _ hfzero)
      exact sub_eq_zero.mp (by simpa only [map_sub] using hdiffi)

end PowerSeries
