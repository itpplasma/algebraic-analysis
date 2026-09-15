/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.BinomialSeriesRoot
import AlgebraicAnalysis.RingTheory.LaurentSeriesCoefficientDerivation
import AlgebraicAnalysis.RingTheory.LaurentSeriesMomentPairing
import Mathlib.Tactic.LinearCombination

/-!
# Normalized negative fractional powers at infinity

For a monic spectral polynomial written as `s^m (1 + u(X))`, with
`X = s⁻¹`, its normalized negative fractional powers have the form
`X^j (1 + u)^(-j/m)`. This file constructs that binomial series and proves
the leading conditions consumed by the finite Laurent moment pairing.

## Provenance

The interface is extracted from `itpplasma/jc2` at revision
`4a7add6104d021c2f2f3b0e903f66d15096b56c9`, file
`research/general-pq-carry-20260911/finite-moment-coordinates-all-m.md`,
equations (3) and (5), graph node `direct-finite-moment-coordinates-all-m`. This Lean
implementation is Apache-2.0; the source repository's license is not asserted
here. Authorship follows the source repository history (Christopher Albert);
this file supplies the reusable Lean implementation. The downstream consumer
is `itpplasma/jc2-formal`, module `JC2Formal/Corner/Moments.lean`.
-/

namespace AlgebraicAnalysis

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The normalized Laurent expansion `X^j (1+u)^(-j/m)`. Consumers use
`m ≠ 0`; keeping the formula total is convenient for coefficient lemmas. -/
def LaurentSeries.monicNegativeFractionalPower
    (u : PowerSeries K) (j m : ℕ) : LaurentSeries K :=
  HahnSeries.single (j : ℤ) 1 *
    HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.binomialSeries K (-((j : K) / (m : K)))).subst u)

/-- The normalized monic Laurent series `X⁻ᵐ (1+u)` associated to a
zero-constant tail. -/
def LaurentSeries.normalizedMonicSeries
    (u : PowerSeries K) (m : ℕ) : LaurentSeries K :=
  HahnSeries.single (-(m : ℤ)) 1 *
    HahnSeries.ofPowerSeries ℤ K (1 + u)

private theorem LaurentSeries.monicNegativeFractionalPower_rootSeries_constantCoeff
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0)
    (j m : ℕ) :
    PowerSeries.constantCoeff
      ((PowerSeries.binomialSeries K (-((j : K) / (m : K)))).subst u) = 1 := by
  have hu' : MvPowerSeries.constantCoeff u = 0 := hu
  change MvPowerSeries.constantCoeff
    ((PowerSeries.binomialSeries K (-((j : K) / (m : K)))).subst u) = 1
  rw [PowerSeries.constantCoeff_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' hu)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [hu', hn]

/-- The normalized negative fractional power has no term below `X^j`. -/
theorem LaurentSeries.monicNegativeFractionalPower_coeff_eq_zero_of_lt
    (u : PowerSeries K) (j m : ℕ) (z : ℤ) (hz : z < j) :
    (LaurentSeries.monicNegativeFractionalPower u j m).coeff z = 0 := by
  rw [LaurentSeries.monicNegativeFractionalPower,
    HahnSeries.coeff_single_mul]
  simp only [one_mul]
  apply LaurentSeries.ofPowerSeries_coeff_of_neg
  omega

/-- A zero-constant tail gives leading coefficient one at `X^j`. -/
theorem LaurentSeries.monicNegativeFractionalPower_coeff_self
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0)
    (j m : ℕ) :
    (LaurentSeries.monicNegativeFractionalPower u j m).coeff j = 1 := by
  rw [LaurentSeries.monicNegativeFractionalPower,
    HahnSeries.coeff_single_mul]
  simp only [one_mul, sub_self]
  rw [show (0 : ℤ) = (0 : ℕ) by rfl,
    HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact
    LaurentSeries.monicNegativeFractionalPower_rootSeries_constantCoeff
      u hu j m

omit [CharZero K] in
/-- The normalized monic Laurent series has no term below `X⁻ᵐ`. -/
theorem LaurentSeries.normalizedMonicSeries_coeff_eq_zero_of_lt
    (u : PowerSeries K) (m : ℕ) (z : ℤ) (hz : z < -(m : ℤ)) :
    (LaurentSeries.normalizedMonicSeries u m).coeff z = 0 := by
  rw [LaurentSeries.normalizedMonicSeries, HahnSeries.coeff_single_mul]
  simp only [one_mul]
  apply LaurentSeries.ofPowerSeries_coeff_of_neg
  omega

omit [CharZero K] in
/-- A zero-constant tail gives leading coefficient one at `X⁻ᵐ`. -/
theorem LaurentSeries.normalizedMonicSeries_coeff_leading
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0) (m : ℕ) :
    (LaurentSeries.normalizedMonicSeries u m).coeff (-(m : ℤ)) = 1 := by
  rw [LaurentSeries.normalizedMonicSeries, HahnSeries.coeff_single_mul]
  simp only [one_mul, sub_self]
  rw [show (0 : ℤ) = (0 : ℕ) by rfl,
    HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [hu]

omit [CharZero K] in
/-- `dF/ds` has leading exponent `1-m` for a normalized monic series. -/
theorem LaurentSeries.normalizedMonicSeries_atInfinityDerivative_coeff_eq_zero_of_lt
    (u : PowerSeries K) (m : ℕ) (z : ℤ)
    (hz : z < 1 - (m : ℤ)) :
    (LaurentSeries.atInfinityDerivative
        (LaurentSeries.normalizedMonicSeries u m)).coeff z = 0 := by
  rw [LaurentSeries.atInfinityDerivative_coeff]
  rw [LaurentSeries.normalizedMonicSeries_coeff_eq_zero_of_lt
    u m (z - 1) (by omega)]
  simp

omit [CharZero K] in
/-- The leading coefficient of `dF/ds` is `m`. -/
theorem LaurentSeries.normalizedMonicSeries_atInfinityDerivative_coeff_leading
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0) (m : ℕ) :
    (LaurentSeries.atInfinityDerivative
        (LaurentSeries.normalizedMonicSeries u m)).coeff
      (1 - (m : ℤ)) = (m : K) := by
  rw [LaurentSeries.atInfinityDerivative_coeff]
  rw [show 1 - (m : ℤ) - 1 = -(m : ℤ) by omega,
    LaurentSeries.normalizedMonicSeries_coeff_leading u hu m]
  push_cast
  ring

/-- The moment factor `(dF/ds) F^(-j/m)` starts in exponent `1-m+j`
with coefficient `m`. -/
theorem LaurentSeries.normalizedMomentFactor_coeff_leading
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0)
    (j m : ℕ) (hm : m ≠ 0) :
    (LaurentSeries.atInfinityDerivative
          (LaurentSeries.normalizedMonicSeries u m) *
        LaurentSeries.monicNegativeFractionalPower u j m).coeff
      (1 - (m : ℤ) + (j : ℤ)) = (m : K) := by
  have h := LaurentSeries.coeff_mul_of_leadingTerms
    (LaurentSeries.atInfinityDerivative
      (LaurentSeries.normalizedMonicSeries u m))
    (LaurentSeries.monicNegativeFractionalPower u j m)
    (1 - (m : ℤ)) (j : ℤ) (m : K) 1
    (LaurentSeries.normalizedMonicSeries_atInfinityDerivative_coeff_eq_zero_of_lt
      u m)
    (LaurentSeries.normalizedMonicSeries_atInfinityDerivative_coeff_leading
      u hu m)
    (by exact_mod_cast (Nat.cast_ne_zero.mpr hm))
    (LaurentSeries.monicNegativeFractionalPower_coeff_eq_zero_of_lt u j m)
    (LaurentSeries.monicNegativeFractionalPower_coeff_self u hu j m)
    one_ne_zero
  simpa using h

/-- The normalized negative fractional power has the expected algebraic
relation with its normalized monic Laurent series. -/
theorem LaurentSeries.monicNegativeFractionalPower_pow_mul_normalizedMonicSeries_pow
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0)
    (j m : ℕ) (hm : m ≠ 0) :
    (LaurentSeries.monicNegativeFractionalPower u j m) ^ m *
        (LaurentSeries.normalizedMonicSeries u m) ^ j = 1 := by
  have hseries :=
    PowerSeries.subst_binomialSeries_neg_div_pow_mul_one_add_pow
      u hu j m hm
  have hmap := congrArg (HahnSeries.ofPowerSeries ℤ K) hseries
  simp only [map_mul, map_pow, map_one] at hmap
  have hsingle_pow (a : ℤ) (n : ℕ) :
      (HahnSeries.single a (1 : K)) ^ n =
        HahnSeries.single ((n : ℤ) * a) 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih, HahnSeries.single_mul_single]
        congr 2
        · push_cast
          ring
        · simp
  rw [LaurentSeries.monicNegativeFractionalPower,
    LaurentSeries.normalizedMonicSeries, mul_pow, mul_pow]
  calc
    _ =
        ((HahnSeries.single (j : ℤ) (1 : K)) ^ m *
          (HahnSeries.single (-(m : ℤ)) (1 : K)) ^ j) *
        ((HahnSeries.ofPowerSeries ℤ K
            ((PowerSeries.binomialSeries K
              (-((j : K) / (m : K)))).subst u)) ^ m *
          (HahnSeries.ofPowerSeries ℤ K (1 + u)) ^ j) := by ring
    _ = 1 := by
      rw [hmap, mul_one, hsingle_pow, hsingle_pow,
        HahnSeries.single_mul_single]
      convert (show HahnSeries.single (0 : ℤ) (1 : K) = 1 by simp) using 1
      ring_nf

/-- The normalized root and monic series satisfy the cross-derivative
compatibility needed by the moment identity. -/
theorem LaurentSeries.monicNegativeFractionalPower_derivative_compatible
    {B : Type*} [CommRing B] [Algebra B K]
    (dwK : Derivation B K K) (u : PowerSeries K)
    (hu : PowerSeries.constantCoeff u = 0)
    (j m : ℕ) (hm : m ≠ 0) :
    LaurentSeries.spectralDerivation B
          (LaurentSeries.monicNegativeFractionalPower u j m) *
        LaurentSeries.coefficientwiseDerivation dwK
          (LaurentSeries.normalizedMonicSeries u m) =
      LaurentSeries.coefficientwiseDerivation dwK
          (LaurentSeries.monicNegativeFractionalPower u j m) *
        LaurentSeries.spectralDerivation B
          (LaurentSeries.normalizedMonicSeries u m) := by
  let F := LaurentSeries.normalizedMonicSeries u m
  let Φ := LaurentSeries.monicNegativeFractionalPower u j m
  let ds : Derivation B (LaurentSeries K) (LaurentSeries K) :=
    LaurentSeries.spectralDerivation B
  let dw : Derivation B (LaurentSeries K) (LaurentSeries K) :=
    LaurentSeries.coefficientwiseDerivation dwK
  have hroot : Φ ^ m * F ^ j = 1 :=
    LaurentSeries.monicNegativeFractionalPower_pow_mul_normalizedMonicSeries_pow
      u hu j m hm
  have hds := congrArg ds hroot
  have hdw := congrArg dw hroot
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, Derivation.map_one_eq_zero] at hds hdw
  have hΦm : Φ ^ m ≠ 0 := by
    intro h
    rw [h, zero_mul] at hroot
    exact zero_ne_one hroot
  have hFj : F ^ j ≠ 0 := by
    intro h
    rw [h, mul_zero] at hroot
    exact zero_ne_one hroot
  have hΦ : Φ ≠ 0 := by
    intro h
    apply hΦm
    simp [h, hm]
  letI : CharZero (LaurentSeries K) :=
    charZero_of_injective_algebraMap (R := K)
      (algebraMap K (LaurentSeries K)).injective
  have hmL : (m : LaurentSeries K) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hpref :
      (m : LaurentSeries K) * Φ ^ (m - 1) * F ^ j ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hmL (pow_ne_zero _ hΦ)) hFj
  have hzero :
      ((m : LaurentSeries K) * Φ ^ (m - 1) * F ^ j) *
        (ds Φ * dw F - dw Φ * ds F) = 0 := by
    linear_combination (dw F) * hds - (ds F) * hdw
  change ds Φ * dw F = dw Φ * ds F
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hpref)

end

end AlgebraicAnalysis
