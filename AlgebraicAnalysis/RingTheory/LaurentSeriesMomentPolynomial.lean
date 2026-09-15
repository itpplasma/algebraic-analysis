/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.LaurentSeriesFractionalPower

/-!
# Polynomial dependence of normalized Laurent moment coefficients

Coefficients of `(dF/ds) F^(-j/m)` are polynomial expressions over `ℚ` in
the positive coefficients of the zero-constant normalized tail `u`.  The
universal expression uses one variable for each coefficient of `u`; every
individual multivariate polynomial still has finite support.

## Provenance

This interface is extracted from `itpplasma/jc2` at revision
`4a7add6104d021c2f2f3b0e903f66d15096b56c9`, file
`research/general-pq-carry-20260911/finite-moment-coordinates-all-m.md`,
equation (5), graph node `direct-finite-moment-coordinates-all-m`.  The
downstream consumer supplies the project-specific finite family `D_i`.
-/

namespace AlgebraicAnalysis

noncomputable section

private abbrev UniversalCoeffPoly := MvPolynomial ℕ ℚ

private def universalCoefficientTail : PowerSeries UniversalCoeffPoly :=
  PowerSeries.mk
    (fun n => if _h : n = 0 then 0 else MvPolynomial.X (n - 1))

private def universalNegativeFractionalRoot (j m : ℕ) :
    PowerSeries UniversalCoeffPoly :=
  (PowerSeries.binomialSeries UniversalCoeffPoly
      (algebraMap ℚ UniversalCoeffPoly (-((j : ℚ) / (m : ℚ))))).subst
    universalCoefficientTail

private def universalNegativeFractionalFactor (j m : ℕ) :
    LaurentSeries UniversalCoeffPoly :=
  HahnSeries.single (j : ℤ) 1 *
    HahnSeries.ofPowerSeries ℤ UniversalCoeffPoly
      (universalNegativeFractionalRoot j m)

private def universalNormalizedMonicSeries (m : ℕ) :
    LaurentSeries UniversalCoeffPoly :=
  HahnSeries.single (-(m : ℤ)) 1 *
    HahnSeries.ofPowerSeries ℤ UniversalCoeffPoly
      (1 + universalCoefficientTail)

private def universalAtInfinityDerivative (m : ℕ) :
    LaurentSeries UniversalCoeffPoly :=
  -(HahnSeries.single 2 1 *
    LaurentSeries.derivative ℤ (universalNormalizedMonicSeries m))

private def universalMomentFactor (j m : ℕ) :
    LaurentSeries UniversalCoeffPoly :=
  universalAtInfinityDerivative m * universalNegativeFractionalFactor j m

private theorem universalCoefficientTail_map
    {K : Type*} [Field K] [CharZero K]
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0) :
    PowerSeries.map
        (MvPolynomial.eval₂Hom (algebraMap ℚ K)
          (fun n : ℕ => u.coeff (n + 1)))
        universalCoefficientTail = u := by
  ext n
  rw [PowerSeries.coeff_map]
  simp only [universalCoefficientTail, PowerSeries.coeff_mk]
  cases n with
  | zero => simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hu.symm
  | succ n => simp

private theorem universalNegativeFractionalRoot_map
    {K : Type*} [Field K] [CharZero K]
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0)
    (j m : ℕ) :
    PowerSeries.map
        (MvPolynomial.eval₂Hom (algebraMap ℚ K)
          (fun n : ℕ => u.coeff (n + 1)))
        (universalNegativeFractionalRoot j m) =
      (PowerSeries.binomialSeries K (-((j : K) / (m : K)))).subst u := by
  let f : UniversalCoeffPoly →+* K :=
    MvPolynomial.eval₂Hom (algebraMap ℚ K)
      (fun n : ℕ => u.coeff (n + 1))
  have htail := universalCoefficientTail_map u hu
  have hsub : PowerSeries.HasSubst universalCoefficientTail := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp [universalCoefficientTail]
  have hmap := PowerSeries.map_subst_binomialSeries f
    (algebraMap ℚ UniversalCoeffPoly (-((j : ℚ) / (m : ℚ))))
    universalCoefficientTail hsub
  change PowerSeries.map f
      ((PowerSeries.binomialSeries UniversalCoeffPoly
        (algebraMap ℚ UniversalCoeffPoly
          (-((j : ℚ) / (m : ℚ))))).subst universalCoefficientTail) = _
  rw [hmap, htail]
  congr 2
  simp [f]

private theorem map_ofPowerSeries
    {K : Type*} [Field K] [CharZero K]
    (f : UniversalCoeffPoly →+* K) (p : PowerSeries UniversalCoeffPoly) :
    (HahnSeries.ofPowerSeries ℤ UniversalCoeffPoly p).map f =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.map f p) := by
  ext z
  cases z with
  | ofNat n => simp [HahnSeries.map_coeff]
  | negSucc n =>
      rw [HahnSeries.map_coeff, HahnSeries.ofPowerSeries_apply,
        HahnSeries.embDomain_of_notMem_range]
      · rw [HahnSeries.ofPowerSeries_apply,
          HahnSeries.embDomain_of_notMem_range]
        · simp
        · rintro ⟨a, ha⟩
          simp at ha
      · rintro ⟨a, ha⟩
        simp at ha

private theorem map_derivative
    {K : Type*} [Field K] [CharZero K]
    (f : UniversalCoeffPoly →+* K) (F : LaurentSeries UniversalCoeffPoly) :
    (LaurentSeries.derivative ℤ F).map f =
      LaurentSeries.derivative ℤ (F.map f) := by
  ext z
  rw [HahnSeries.map_coeff, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, HahnSeries.map_coeff]
  simp

private theorem map_mul
    {K : Type*} [Field K] [CharZero K]
    (f : UniversalCoeffPoly →+* K)
    (x y : LaurentSeries UniversalCoeffPoly) :
    (x * y).map f = x.map f * y.map f :=
  HahnSeries.map_mul f.toNonUnitalRingHom

private theorem map_neg
    {K : Type*} [Field K] [CharZero K]
    (f : UniversalCoeffPoly →+* K) (x : LaurentSeries UniversalCoeffPoly) :
    (-x).map f = -x.map f :=
  HahnSeries.map_neg f.toAddMonoidHom

private theorem map_single
    {K : Type*} [Field K] [CharZero K]
    (f : UniversalCoeffPoly →+* K) {a : ℤ} (r : UniversalCoeffPoly) :
    ((HahnSeries.single a) r).map f = (HahnSeries.single a) (f r) :=
  HahnSeries.map_single f.toZeroHom

private theorem universalNormalizedMonicSeries_map
    {K : Type*} [Field K] [CharZero K]
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0) (m : ℕ) :
    (universalNormalizedMonicSeries m).map
        (MvPolynomial.eval₂Hom (algebraMap ℚ K)
          (fun n : ℕ => u.coeff (n + 1))) =
      LaurentSeries.normalizedMonicSeries u m := by
  let f : UniversalCoeffPoly →+* K :=
    MvPolynomial.eval₂Hom (algebraMap ℚ K)
      (fun n : ℕ => u.coeff (n + 1))
  change (universalNormalizedMonicSeries m).map f = _
  rw [universalNormalizedMonicSeries, map_mul f, map_single f,
    map_ofPowerSeries]
  change HahnSeries.single (-(m : ℤ)) (f 1) *
      HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map f (1 + universalCoefficientTail)) = _
  rw [map_add, universalCoefficientTail_map u hu]
  simp [LaurentSeries.normalizedMonicSeries, f]

private theorem universalNegativeFractionalFactor_map
    {K : Type*} [Field K] [CharZero K]
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0)
    (j m : ℕ) :
    (universalNegativeFractionalFactor j m).map
        (MvPolynomial.eval₂Hom (algebraMap ℚ K)
          (fun n : ℕ => u.coeff (n + 1))) =
      LaurentSeries.monicNegativeFractionalPower u j m := by
  let f : UniversalCoeffPoly →+* K :=
    MvPolynomial.eval₂Hom (algebraMap ℚ K)
      (fun n : ℕ => u.coeff (n + 1))
  change (universalNegativeFractionalFactor j m).map f = _
  rw [universalNegativeFractionalFactor, map_mul f, map_single f,
    map_ofPowerSeries, universalNegativeFractionalRoot_map u hu]
  simp [LaurentSeries.monicNegativeFractionalPower, f]

private theorem universalAtInfinityDerivative_map
    {K : Type*} [Field K] [CharZero K]
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0) (m : ℕ) :
    (universalAtInfinityDerivative m).map
        (MvPolynomial.eval₂Hom (algebraMap ℚ K)
          (fun n : ℕ => u.coeff (n + 1))) =
      LaurentSeries.atInfinityDerivative
        (LaurentSeries.normalizedMonicSeries u m) := by
  let f : UniversalCoeffPoly →+* K :=
    MvPolynomial.eval₂Hom (algebraMap ℚ K)
      (fun n : ℕ => u.coeff (n + 1))
  change (universalAtInfinityDerivative m).map f = _
  rw [universalAtInfinityDerivative, map_neg f, map_mul f, map_single f,
    map_derivative f, universalNormalizedMonicSeries_map u hu]
  simp [LaurentSeries.atInfinityDerivative, f]

private theorem universalMomentFactor_map
    {K : Type*} [Field K] [CharZero K]
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0)
    (j m : ℕ) :
    (universalMomentFactor j m).map
        (MvPolynomial.eval₂Hom (algebraMap ℚ K)
          (fun n : ℕ => u.coeff (n + 1))) =
      LaurentSeries.atInfinityDerivative
          (LaurentSeries.normalizedMonicSeries u m) *
        LaurentSeries.monicNegativeFractionalPower u j m := by
  let f : UniversalCoeffPoly →+* K :=
    MvPolynomial.eval₂Hom (algebraMap ℚ K)
      (fun n : ℕ => u.coeff (n + 1))
  change (universalMomentFactor j m).map f = _
  rw [universalMomentFactor, map_mul f,
    universalAtInfinityDerivative_map u hu,
    universalNegativeFractionalFactor_map u hu]

/-- The universal multivariate polynomial for coefficient `z` of the
normalized moment factor `(dF/ds)F^(-j/m)`. Variable `n` represents the
positive tail coefficient `u_(n+1)`. The definition is total at `m = 0`;
its literal fractional-power interpretation requires `m ≠ 0`. -/
def LaurentSeries.normalizedMomentFactorCoefficientPolynomial
    (j m : ℕ) (z : ℤ) : MvPolynomial ℕ ℚ :=
  (universalMomentFactor j m).coeff z

/-- Evaluating the single universal polynomial
`normalizedMomentFactorCoefficientPolynomial j m z` at the positive
coefficients of any zero-constant tail gives coefficient `z` of
`(dF/ds)F^(-j/m)`. The identity is algebraically valid at `m = 0`; its
fractional-power interpretation requires `m ≠ 0`. -/
theorem LaurentSeries.eval_normalizedMomentFactorCoefficientPolynomial
    {K : Type*} [Field K] [CharZero K]
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u = 0)
    (j m : ℕ) (z : ℤ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ K)
        (fun n : ℕ => u.coeff (n + 1))
        (LaurentSeries.normalizedMomentFactorCoefficientPolynomial j m z) =
      (LaurentSeries.atInfinityDerivative
          (LaurentSeries.normalizedMonicSeries u m) *
        LaurentSeries.monicNegativeFractionalPower u j m).coeff z := by
  have hmap := universalMomentFactor_map u hu j m
  have hcoeff := congrArg (fun x : LaurentSeries K => x.coeff z) hmap
  rw [HahnSeries.map_coeff] at hcoeff
  simpa [LaurentSeries.normalizedMomentFactorCoefficientPolynomial] using hcoeff

end

end AlgebraicAnalysis
