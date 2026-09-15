/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.LaurentSeriesMomentPolynomial

namespace AlgebraicAnalysisTest.LaurentSeriesMomentPolynomial

open AlgebraicAnalysis

noncomputable section

private def cubicTail : PowerSeries ℚ :=
  PowerSeries.C 2 * PowerSeries.X ^ 2 +
    PowerSeries.C 3 * PowerSeries.X ^ 3

private theorem choose_neg_third_two : Ring.choose (-(1 / 3 : ℚ)) 2 = 2 / 9 := by
  rw [Ring.choose]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer
    (-(1 / 3 : ℚ) - 2 + 1) 2
  rw [show 2 = 1 + 1 by omega, ascPochhammer_succ_left,
    ascPochhammer_one, Polynomial.smeval_X_mul, Polynomial.smeval_comp,
    Polynomial.smeval_add, Polynomial.smeval_X, Polynomial.smeval_one] at h
  norm_num at h ⊢
  linarith

private theorem root_coeff_two :
    (LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 2 = 0 := by
  norm_num [LaurentSeries.monicNegativeFractionalPower, HahnSeries.coeff_single_mul,
    PowerSeries.subst_X]
  rw [show (1 : ℤ) = (1 : ℕ) by rfl,
    HahnSeries.ofPowerSeries_apply_coeff]
  rw [PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' (by norm_num [cubicTail]))]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 1)]
  · norm_num [PowerSeries.binomialSeries_coeff, Finset.sum_range_succ]
  · intro d hd
    simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at hd ⊢
    by_contra hnot
    have hd1 : 1 ≤ d := by omega
    apply hd
    rw [show cubicTail = PowerSeries.X ^ 2 *
        (PowerSeries.C 2 + PowerSeries.C 3 * PowerSeries.X) by
      simp [cubicTail, mul_add]; ring]
    rw [mul_pow, ← pow_mul]
    simp [PowerSeries.coeff_X_pow_mul', show 1 < 2 * d by omega]

private theorem root_coeff_three :
    (LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 3 = -(2 / 3) := by
  norm_num [LaurentSeries.monicNegativeFractionalPower, HahnSeries.coeff_single_mul,
    PowerSeries.subst_X]
  rw [show (2 : ℤ) = (2 : ℕ) by rfl,
    HahnSeries.ofPowerSeries_apply_coeff]
  rw [PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' (by norm_num [cubicTail]))]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 2)]
  · have ht : PowerSeries.coeff 2 cubicTail = 2 := by
      norm_num [cubicTail, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    norm_num [PowerSeries.binomialSeries_coeff, Finset.sum_range_succ, ht]
  · intro d hd
    simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at hd ⊢
    by_contra hnot
    have hd2 : 2 ≤ d := by omega
    apply hd
    rw [show cubicTail = PowerSeries.X ^ 2 *
        (PowerSeries.C 2 + PowerSeries.C 3 * PowerSeries.X) by
      simp [cubicTail, mul_add]; ring]
    rw [mul_pow, ← pow_mul]
    simp [PowerSeries.coeff_X_pow_mul', show ¬2 * d ≤ 2 by omega]

private theorem root_coeff_four :
    (LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 4 = -1 := by
  norm_num [LaurentSeries.monicNegativeFractionalPower, HahnSeries.coeff_single_mul,
    PowerSeries.subst_X]
  rw [show (3 : ℤ) = (3 : ℕ) by rfl,
    HahnSeries.ofPowerSeries_apply_coeff]
  rw [PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' (by norm_num [cubicTail]))]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 3)]
  · have ht : PowerSeries.coeff 3 cubicTail = 3 := by
      norm_num [cubicTail, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    have hsq : PowerSeries.coeff 3 (cubicTail ^ 2) = 0 := by
      rw [show cubicTail = PowerSeries.X ^ 2 *
          (PowerSeries.C 2 + PowerSeries.C 3 * PowerSeries.X) by
        simp [cubicTail, mul_add]; ring]
      rw [mul_pow, ← pow_mul]
      simp [PowerSeries.coeff_X_pow_mul']
    norm_num [PowerSeries.binomialSeries_coeff, Finset.sum_range_succ, hsq, ht]
  · intro d hd
    simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at hd ⊢
    by_contra hnot
    have hd3 : 3 ≤ d := by omega
    apply hd
    rw [show cubicTail = PowerSeries.X ^ 2 *
        (PowerSeries.C 2 + PowerSeries.C 3 * PowerSeries.X) by
      simp [cubicTail, mul_add]; ring]
    rw [mul_pow, ← pow_mul]
    simp [PowerSeries.coeff_X_pow_mul', show 3 < 2 * d by omega]

private theorem root_coeff_five :
    (LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 5 = 8 / 9 := by
  norm_num [LaurentSeries.monicNegativeFractionalPower, HahnSeries.coeff_single_mul,
    PowerSeries.subst_X]
  rw [show (4 : ℤ) = (4 : ℕ) by rfl,
    HahnSeries.ofPowerSeries_apply_coeff]
  rw [PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' (by norm_num [cubicTail]))]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 3)]
  · have ht : PowerSeries.coeff 4 cubicTail = 0 := by
      norm_num [cubicTail, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    have hsq : PowerSeries.coeff 4 (cubicTail ^ 2) = 4 := by
      rw [show cubicTail = PowerSeries.X ^ 2 *
          (PowerSeries.C 2 + PowerSeries.C 3 * PowerSeries.X) by
        simp [cubicTail, mul_add]; ring]
      rw [mul_pow, ← pow_mul]
      norm_num [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_zero_eq_constantCoeff_apply]
    norm_num [PowerSeries.binomialSeries_coeff, Finset.sum_range_succ,
      hsq, ht, choose_neg_third_two]
  · intro d hd
    simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at hd ⊢
    by_contra hnot
    have hd3 : 3 ≤ d := by omega
    apply hd
    rw [show cubicTail = PowerSeries.X ^ 2 *
        (PowerSeries.C 2 + PowerSeries.C 3 * PowerSeries.X) by
      simp [cubicTail, mul_add]; ring]
    rw [mul_pow, ← pow_mul]
    simp [PowerSeries.coeff_X_pow_mul', show 4 < 2 * d by omega]

private theorem derivative_cubicTail :
    LaurentSeries.atInfinityDerivative
        (LaurentSeries.normalizedMonicSeries cubicTail 3) =
      HahnSeries.single (-2) 3 + HahnSeries.single 0 2 := by
  have hcoeff (n : ℕ) (w : ℤ) :
      (n : LaurentSeries ℚ).coeff w = if w = 0 then n else 0 := by
    rw [← HahnSeries.single_zero_natCast]
    simp [HahnSeries.coeff_single]
  have hcoeff_two (w : ℤ) :
      (2 : LaurentSeries ℚ).coeff w = if w = 0 then (2 : ℚ) else 0 := by
    simpa using hcoeff 2 w
  have hcoeff_three (w : ℤ) :
      (3 : LaurentSeries ℚ).coeff w = if w = 0 then (3 : ℚ) else 0 := by
    simpa using hcoeff 3 w
  ext z
  rw [LaurentSeries.atInfinityDerivative_coeff]
  norm_num [LaurentSeries.normalizedMonicSeries, HahnSeries.coeff_single_mul,
    HahnSeries.coeff_mul_single, LaurentSeries.hasseDeriv_coeff, cubicTail]
  simp only [hcoeff_two, hcoeff_three, HahnSeries.coeff_single]
  split_ifs <;> norm_num at * <;> (try omega) <;> norm_cast <;> omega

private theorem moment_coeff_two :
    (LaurentSeries.atInfinityDerivative
          (LaurentSeries.normalizedMonicSeries cubicTail 3) *
        LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 2 = -3 := by
  rw [derivative_cubicTail, add_mul]
  change
    ((HahnSeries.single (-2) 3 *
        LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 2) +
      ((HahnSeries.single 0 2 *
        LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 2) = -3
  rw [HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul]
  norm_num only
  rw [root_coeff_four, root_coeff_two]
  norm_num

private theorem moment_coeff_three :
    (LaurentSeries.atInfinityDerivative
          (LaurentSeries.normalizedMonicSeries cubicTail 3) *
        LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 3 = 4 / 3 := by
  rw [derivative_cubicTail, add_mul]
  change
    ((HahnSeries.single (-2) 3 *
        LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 3) +
      ((HahnSeries.single 0 2 *
        LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 3) = 4 / 3
  rw [HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul]
  norm_num only
  rw [root_coeff_five, root_coeff_three]
  norm_num

/-- Hostile input control: the test tail is nonzero in two distinct depressed
coefficients and has no constant or linear term. -/
example :
    PowerSeries.constantCoeff cubicTail = 0 ∧
      cubicTail.coeff 1 = 0 ∧ cubicTail.coeff 2 = 2 ∧ cubicTail.coeff 3 = 3 := by
  norm_num [cubicTail, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

/-- The universal polynomial specializes to a nontrivial cubic-tail moment
coefficient, not only to the leading coefficient. -/
example :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℚ)
        (fun n : ℕ => cubicTail.coeff (n + 1))
        (LaurentSeries.normalizedMomentFactorCoefficientPolynomial 1 3 2) =
      (LaurentSeries.atInfinityDerivative
          (LaurentSeries.normalizedMonicSeries cubicTail 3) *
        LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 2 := by
  exact LaurentSeries.eval_normalizedMomentFactorCoefficientPolynomial
    cubicTail (by norm_num [cubicTail]) 1 3 2

/-- Numerical hostile control away from the leading term. -/
example :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℚ)
        (fun n : ℕ => cubicTail.coeff (n + 1))
        (LaurentSeries.normalizedMomentFactorCoefficientPolynomial 1 3 2) = -3 := by
  calc
    _ = (LaurentSeries.atInfinityDerivative
          (LaurentSeries.normalizedMonicSeries cubicTail 3) *
        LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 2 :=
      LaurentSeries.eval_normalizedMomentFactorCoefficientPolynomial
        cubicTail (by norm_num [cubicTail]) 1 3 2
    _ = -3 := moment_coeff_two

/-- Nonlinear hostile control: this coefficient contains a quadratic tail term. -/
example :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℚ)
        (fun n : ℕ => cubicTail.coeff (n + 1))
        (LaurentSeries.normalizedMomentFactorCoefficientPolynomial 1 3 3) = 4 / 3 := by
  calc
    _ = (LaurentSeries.atInfinityDerivative
          (LaurentSeries.normalizedMonicSeries cubicTail 3) *
        LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff 3 :=
      LaurentSeries.eval_normalizedMomentFactorCoefficientPolynomial
        cubicTail (by norm_num [cubicTail]) 1 3 3
    _ = 4 / 3 := moment_coeff_three

/-- Orientation control: at the leading exponent `1-m+j=-1`, the specialized
polynomial evaluates to the monic derivative coefficient `m=3`. -/
example :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℚ)
        (fun n : ℕ => cubicTail.coeff (n + 1))
        (LaurentSeries.normalizedMomentFactorCoefficientPolynomial 1 3 (-1)) = 3 := by
  calc
    _ = (LaurentSeries.atInfinityDerivative
          (LaurentSeries.normalizedMonicSeries cubicTail 3) *
        LaurentSeries.monicNegativeFractionalPower cubicTail 1 3).coeff (-1) :=
      LaurentSeries.eval_normalizedMomentFactorCoefficientPolynomial
        cubicTail (by norm_num [cubicTail]) 1 3 (-1)
    _ = 3 := LaurentSeries.normalizedMomentFactor_coeff_leading
      cubicTail (by norm_num [cubicTail]) 1 3 (by norm_num)

#print axioms AlgebraicAnalysis.LaurentSeries.normalizedMomentFactorCoefficientPolynomial
#print axioms AlgebraicAnalysis.LaurentSeries.eval_normalizedMomentFactorCoefficientPolynomial

end


end AlgebraicAnalysisTest.LaurentSeriesMomentPolynomial
