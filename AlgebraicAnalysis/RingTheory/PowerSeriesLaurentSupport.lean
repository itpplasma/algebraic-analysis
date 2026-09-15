/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.RingTheory.LaurentSeries

/-!
# Affine support bounds for power series with Laurent coefficients

This file packages lower affine support bounds for a power series in one
variable whose coefficients are Laurent series in another. The mixed-slope
product lemmas isolate the finite-truncation argument used when a discarded
Laurent remainder starts in strictly positive degree.
-/

noncomputable section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The coefficient at outer index `ell` vanishes below the affine inner
support line `2*z = a*ell+b`. -/
def LaurentAffineLower (a b : ℤ) (s : PowerSeries (LaurentSeries R)) : Prop :=
  ∀ ell : ℕ, ∀ z : ℤ,
    2 * z < a * (ell : ℤ) + b → (s.coeff ell).coeff z = 0

namespace LaurentAffineLower

theorem zero :
    LaurentAffineLower a b (0 : PowerSeries (LaurentSeries R)) := by
  intro ell z hz
  simp

theorem add {a b : ℤ} {s t : PowerSeries (LaurentSeries R)}
    (hs : LaurentAffineLower a b s) (ht : LaurentAffineLower a b t) :
    LaurentAffineLower a b (s + t) := by
  intro ell z hz
  change ((s.coeff ell + t.coeff ell).coeff z) = 0
  rw [HahnSeries.coeff_add, hs ell z hz, ht ell z hz]
  simp

theorem mul {a b d : ℤ} {s t : PowerSeries (LaurentSeries R)}
    (hs : LaurentAffineLower a b s) (ht : LaurentAffineLower a d t) :
    LaurentAffineLower a (b + d) (s * t) := by
  classical
  intro ell z hz
  change ((s * t).coeff ell).coeff z = 0
  rw [PowerSeries.coeff_mul, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro p hp
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  simp only [Finset.mem_antidiagonal] at hp hij
  have hpz : (p.1 : ℤ) + (p.2 : ℤ) = (ell : ℤ) := by
    have hp' : p.1 + p.2 = ell :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    omega
  by_cases h₁ : 2 * ij.1 < a * (p.1 : ℤ) + b
  · rw [hs p.1 ij.1 h₁]
    simp
  by_cases h₂ : 2 * ij.2 < a * (p.2 : ℤ) + d
  · rw [ht p.2 ij.2 h₂]
    simp
  have h₁' : a * (p.1 : ℤ) + b ≤ 2 * ij.1 := le_of_not_gt h₁
  have h₂' : a * (p.2 : ℤ) + d ≤ 2 * ij.2 := le_of_not_gt h₂
  have hbound :
      a * (ell : ℤ) + (b + d) =
        (a * (p.1 : ℤ) + b) + (a * (p.2 : ℤ) + d) := by
    rw [← hpz]
    ring
  have hz' : 2 * (ij.1 + ij.2) <
      (a * (p.1 : ℤ) + b) + (a * (p.2 : ℤ) + d) := by
    rw [hij.2.2]
    calc
      2 * z < a * (ell : ℤ) + (b + d) := hz
      _ = _ := hbound
  exfalso
  linarith

/-- Multiplication by a nonnegative-slope factor preserves zero slope on the
left while adding the intercept bounds. -/
theorem mul_zero_left {a b d : ℤ} {s t : PowerSeries (LaurentSeries R)}
    (ha : 0 ≤ a) (hs : LaurentAffineLower 0 b s)
    (ht : LaurentAffineLower a d t) :
    LaurentAffineLower 0 (b + d) (s * t) := by
  classical
  intro ell z hz
  change ((s * t).coeff ell).coeff z = 0
  rw [PowerSeries.coeff_mul, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro p hp
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  simp only [Finset.mem_antidiagonal] at hij
  by_cases h₁ : 2 * ij.1 < 0 * (p.1 : ℤ) + b
  · rw [hs p.1 ij.1 h₁]
    simp
  by_cases h₂ : 2 * ij.2 < a * (p.2 : ℤ) + d
  · rw [ht p.2 ij.2 h₂]
    simp
  have h₁' : b ≤ 2 * ij.1 := by simpa using le_of_not_gt h₁
  have h₂' : a * (p.2 : ℤ) + d ≤ 2 * ij.2 := le_of_not_gt h₂
  have hp2 : (0 : ℤ) ≤ (p.2 : ℤ) := by positivity
  have hapos : 0 ≤ a * (p.2 : ℤ) := mul_nonneg ha hp2
  exfalso
  linarith [hij.2.2]

/-- Right-handed form of `mul_zero_left`. -/
theorem mul_zero_right {a b d : ℤ} {s t : PowerSeries (LaurentSeries R)}
    (ha : 0 ≤ a) (hs : LaurentAffineLower a b s)
    (ht : LaurentAffineLower 0 d t) :
    LaurentAffineLower 0 (b + d) (s * t) := by
  simpa only [mul_comm, add_comm] using mul_zero_left ha ht hs

theorem one (a : ℤ) :
    LaurentAffineLower a 0 (1 : PowerSeries (LaurentSeries R)) := by
  intro ell z hz
  by_cases hell : ell = 0
  · subst ell
    simp only [PowerSeries.coeff_one, ↓reduceIte]
    by_cases hz0 : z = 0
    · subst z
      exfalso
      omega
    · simp [hz0]
  · simp [PowerSeries.coeff_one, hell]

theorem pow {a b : ℤ} {s : PowerSeries (LaurentSeries R)}
    (hs : LaurentAffineLower a b s) : ∀ n : ℕ,
      LaurentAffineLower a ((n : ℤ) * b) (s ^ n) := by
  intro n
  induction n with
  | zero => simpa using one a
  | succ n ih =>
      have hmul := mul ih hs
      simpa [pow_succ, Nat.cast_succ, add_mul, mul_add, add_assoc,
        add_comm, add_left_comm] using hmul

/-- If two series have the same affine lower support and their difference
starts in strictly positive inner Laurent degree, then the difference of
their powers has the corresponding zero-slope lower bound. -/
theorem pow_sub {D : ℤ} {s t : PowerSeries (LaurentSeries R)}
    (hs : LaurentAffineLower 1 (-D) s) (ht : LaurentAffineLower 1 (-D) t)
    (hdiff : LaurentAffineLower 0 2 (s - t)) : ∀ n : ℕ,
      LaurentAffineLower 0 (((n : ℤ) - 1) * (-D) + 2) (s ^ n - t ^ n) := by
  intro n
  induction n with
  | zero =>
      simpa [pow_zero] using
        (zero : LaurentAffineLower 0 (((0 : ℤ) - 1) * (-D) + 2)
          (0 : PowerSeries (LaurentSeries R)))
  | succ n ih =>
      have hleft := mul_zero_left (by norm_num : (0 : ℤ) ≤ 1) ih hs
      have hright := mul_zero_right (by norm_num : (0 : ℤ) ≤ 1) (pow ht n) hdiff
      have hleft' :
          LaurentAffineLower 0 ((((n : ℤ) - 1) * (-D) + 2) + (-D))
            ((s ^ n - t ^ n) * s) := hleft
      have hright' :
          LaurentAffineLower 0 ((((n : ℤ) - 1) * (-D) + 2) + (-D))
            (t ^ n * (s - t)) := by
        convert hright using 1 <;> ring
      have hadd := add hleft' hright'
      convert hadd using 1 <;> simp only [Nat.cast_succ, pow_succ]
      · ring
      · ring

/-- Coefficients in the explicit negative range agree after taking powers. -/
theorem pow_sub_coeff_zero_of_ge
    (D n ell K : ℕ) {s t : PowerSeries (LaurentSeries R)}
    (hs : LaurentAffineLower 1 (-(D : ℤ)) s)
    (ht : LaurentAffineLower 1 (-(D : ℤ)) t)
    (hdiff : LaurentAffineLower 0 2 (s - t))
    (hK : (n - 1) * D ≤ 2 * K) :
    ((s ^ n - t ^ n).coeff ell).coeff (-(K : ℤ)) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
      have hK0 : n * D ≤ 2 * K := by simpa using hK
      have hKneg : -2 * (K : ℤ) ≤ -(n : ℤ) * (D : ℤ) := by
        have hK' : (n : ℤ) * (D : ℤ) ≤ 2 * (K : ℤ) := by
          exact_mod_cast hK0
        linarith
      apply (pow_sub hs ht hdiff (Nat.succ n)) ell (-(K : ℤ))
      calc
        2 * (-(K : ℤ)) = -2 * (K : ℤ) := by ring
        _ ≤ -(n : ℤ) * (D : ℤ) := hKneg
        _ < (n : ℤ) * (-(D : ℤ)) + 2 := by linarith
        _ = 0 * (ell : ℤ) + ((((Nat.succ n : ℕ) : ℤ) - 1) *
              (-(D : ℤ)) + 2) := by
          simp only [Nat.cast_succ]
          ring

end LaurentAffineLower

end PowerSeries
