import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Fractional binomial roots after substitution

This file records the formal identity behind fractional roots of a power
series with constant term one.  A zero-constant tail may be substituted into
the binomial series, and the resulting series has the expected integral power.
-/

noncomputable section

namespace PowerSeries

variable {K : Type*} [CommRing K] [BinomialRing K]

/-- Mapping the coefficient ring of a binomial series maps its exponent. -/
theorem map_binomialSeries {L : Type*} [CommRing L] [BinomialRing L]
    (f : K →+* L) (q : K) :
    PowerSeries.map f (binomialSeries K q) = binomialSeries L (f q) := by
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff]
  simp [smul_eq_mul, Ring.map_choose]

/-- Coefficient-ring maps commute with a substituted binomial series. -/
theorem map_subst_binomialSeries {L : Type*} [CommRing L] [BinomialRing L]
    (f : K →+* L) (q : K) (u : K⟦X⟧) (hu : HasSubst u) :
    PowerSeries.map f ((binomialSeries K q).subst u) =
      (binomialSeries L (f q)).subst (PowerSeries.map f u) := by
  change MvPowerSeries.map f ((binomialSeries K q).subst u) =
    (binomialSeries L (f q)).subst (MvPowerSeries.map f u)
  rw [PowerSeries.map_subst hu, map_binomialSeries]

/-- An integral power of a binomial series multiplies its exponent. -/
theorem binomialSeries_pow_nat (q : K) (m : ℕ) :
    (binomialSeries K q) ^ m = binomialSeries K ((m : K) * q) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, ← binomialSeries_add]
      congr 2
      push_cast
      ring

/-- Substitution preserves the integral-power identity when the scaled
binomial exponent is the natural number `j`. -/
theorem subst_binomialSeries_pow_of_mul_eq
    (u : K⟦X⟧) (hu : constantCoeff u = 0)
    (m j : ℕ) (q : K) (hq : (m : K) * q = (j : K)) :
    ((binomialSeries K q).subst u) ^ m =
      (((1 : K⟦X⟧) + X) ^ j).subst u := by
  have huSubst : HasSubst u := HasSubst.of_constantCoeff_zero' hu
  rw [← subst_pow huSubst, binomialSeries_pow_nat, hq, binomialSeries_nat]

/-- A zero-constant tail substituted into a binomial series gives the
expected integral power of `1 + u`. -/
theorem subst_binomialSeries_pow_eq_one_add_pow_of_mul_eq
    (u : K⟦X⟧) (hu : constantCoeff u = 0)
    (m j : ℕ) (q : K) (hq : (m : K) * q = (j : K)) :
    ((binomialSeries K q).subst u) ^ m = (1 + u) ^ j := by
  have huSubst : HasSubst u := HasSubst.of_constantCoeff_zero' hu
  rw [subst_binomialSeries_pow_of_mul_eq u hu m j q hq,
    subst_pow huSubst, subst_add huSubst, subst_X huSubst]
  have hone : (1 : K⟦X⟧).subst u = 1 := by
    rw [← coe_substAlgHom huSubst]
    simp
  rw [hone]

section Field

variable {L : Type*} [Field L] [CharZero L]

/-- Field specialization with the fractional exponent written as `j / m`. -/
theorem subst_binomialSeries_div_pow
    (u : L⟦X⟧) (hu : constantCoeff u = 0) (j m : ℕ) (hm : m ≠ 0) :
    ((binomialSeries L ((j : L) / (m : L))).subst u) ^ m = (1 + u) ^ j := by
  apply subst_binomialSeries_pow_eq_one_add_pow_of_mul_eq
    u hu m j ((j : L) / (m : L))
  field_simp

end Field

end PowerSeries
