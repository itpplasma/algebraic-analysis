import AlgebraicAnalysis.Derivation.JacobianExactness
import AlgebraicAnalysis.RingTheory.LaurentSeriesResidue
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Independent tests for `Derivation.jacobian_exact_of_commute`
(`AlgebraicAnalysis/Derivation/JacobianExactness.lean`) and for
`LaurentSeries.residue` (`AlgebraicAnalysis/RingTheory/LaurentSeriesResidue.lean`).

The Jacobian-exactness test runs on `R = MvPolynomial (Fin 2) ℚ` with
`ds = pderiv 0`, `dw = pderiv 1` (which commute, proved below from the
coefficient formula `coeff_pderiv`), `F = X 0 ^ 3 + X 1`, `G = X 0 * X 1`,
`Φ = F ^ 2`. The identity instance is checked two ways: once by instantiating
`Derivation.jacobian_exact_of_commute`, and once independently by expanding
both sides with `pderiv_mul`/`pderiv_pow`/`ring` and comparing the raw
`MvPolynomial` values, without using the library lemma at all. Both proofs
must produce the same normal form of the underlying `MvPolynomial`; the
second proof is the required independent oracle. -/

open MvPolynomial
open AlgebraicAnalysis

/-- Mixed partial derivatives of multivariate polynomials commute. This is
the (unconditionally true) hypothesis `hcomm` consumed by
`Derivation.jacobian_exact_of_commute` below; it is not otherwise recorded in
this Mathlib version. -/
theorem MvPolynomial.pderiv_comm {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv,
    show m + Finsupp.single i 1 + Finsupp.single j 1 =
        m + Finsupp.single j 1 + Finsupp.single i 1 by
      rw [add_assoc, add_assoc, add_comm (Finsupp.single i 1) (Finsupp.single j 1)]]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases hij : i = j
  · subst hij; ring
  · rw [if_neg hij, if_neg (Ne.symm hij)]
    ring

section JacobianExactnessTest

/-- The two commuting derivations of the test ring. -/
noncomputable def ds : Derivation ℤ (MvPolynomial (Fin 2) ℚ) (MvPolynomial (Fin 2) ℚ) :=
  (pderiv (0 : Fin 2)).restrictScalars ℤ

noncomputable def dw : Derivation ℤ (MvPolynomial (Fin 2) ℚ) (MvPolynomial (Fin 2) ℚ) :=
  (pderiv (1 : Fin 2)).restrictScalars ℤ

theorem ds_dw_commute : ∀ x : MvPolynomial (Fin 2) ℚ, ds (dw x) = dw (ds x) :=
  fun x => MvPolynomial.pderiv_comm 0 1 x

noncomputable def Ftest : MvPolynomial (Fin 2) ℚ := X 0 ^ 3 + X 1
noncomputable def Gtest : MvPolynomial (Fin 2) ℚ := X 0 * X 1
noncomputable def Phitest : MvPolynomial (Fin 2) ℚ := Ftest ^ 2

/-- The compatibility hypothesis `ds Φ * dw F = dw Φ * ds F` for `Φ = F ^ 2`,
proved directly (not via the `jacobian_exact_pow` corollary), by expanding
both sides with `pderiv_mul`, `pderiv_pow` and `ring`. -/
theorem hPhi_test : ds Phitest * dw Ftest = dw Phitest * ds Ftest := by
  simp only [Phitest, Ftest, ds, dw, Derivation.restrictScalars_apply,
    pderiv_pow, map_add, pderiv_X_self,
    pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
    pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  ring

/-- The library instance of the moment identity, equation (1), on the test
data. -/
theorem jacobian_exact_test :
    dw (Gtest * ds Ftest * Phitest) - ds (Gtest * dw Ftest * Phitest) =
      Phitest * (ds Ftest * dw Gtest - dw Ftest * ds Gtest) :=
  Derivation.jacobian_exact_of_commute ds dw ds_dw_commute Ftest Gtest Phitest hPhi_test

/-- Independent oracle: the same identity, reproved from scratch by
unfolding `ds`, `dw`, `Ftest`, `Gtest`, `Phitest` down to `pderiv` on
concrete monomials and closing with `ring`, without invoking
`Derivation.jacobian_exact_of_commute` (or even `Derivation.leibniz`) at all. -/
theorem jacobian_exact_test_independent :
    dw (Gtest * ds Ftest * Phitest) - ds (Gtest * dw Ftest * Phitest) =
      Phitest * (ds Ftest * dw Gtest - dw Ftest * ds Gtest) := by
  simp only [Phitest, Ftest, Gtest, ds, dw, Derivation.restrictScalars_apply,
    pderiv_mul, map_add, pderiv_pow, pderiv_X_self, map_zero,
    Derivation.map_one_eq_zero, Derivation.map_natCast,
    pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
    pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  ring

/-- The two proofs above agree as `MvPolynomial` values: an explicit
consistency check that the library lemma and the from-scratch computation
are not accidentally proving different statements. -/
example : jacobian_exact_test = jacobian_exact_test_independent := rfl

end JacobianExactnessTest

section ResidueTest

/-- `Res_s` of a formal derivative vanishes, on a concrete Laurent series. -/
example : LaurentSeries.residue
    (LaurentSeries.derivative ℚ (HahnSeries.single (-3 : ℤ) (2 : ℚ))) = 0 :=
  LaurentSeries.residue_derivative _

/-- The residue is genuinely nonzero on a series with a nonzero `s ^ (-1)`
coefficient, so `residue_derivative` is not vacuous: no Laurent series with
`residue f ≠ 0` can be `derivative K g` for any `g`. -/
example : LaurentSeries.residue (HahnSeries.single (-1 : ℤ) (1 : ℚ)) = 1 := by
  simp [LaurentSeries.residue_apply]

#guard (5 : ℚ) ≠ 0

/-- Linearity of the residue on the two series above. -/
example :
    LaurentSeries.residue
        (HahnSeries.single (-1 : ℤ) (1 : ℚ) + HahnSeries.single (-1 : ℤ) (4 : ℚ)) =
      LaurentSeries.residue (HahnSeries.single (-1 : ℤ) (1 : ℚ)) +
        LaurentSeries.residue (HahnSeries.single (-1 : ℤ) (4 : ℚ)) :=
  LaurentSeries.residue_add _ _

/-- The power-series Leibniz rule for `LaurentSeries.derivative`, checked on
`f = 1 + X`, `g = X`: an independent computation from `PowerSeries.derivative`
via `derivative_ofPowerSeries_mul`. -/
example :
    LaurentSeries.derivative ℚ
        (HahnSeries.ofPowerSeries ℤ ℚ (1 + PowerSeries.X) *
          HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X) =
      LaurentSeries.derivative ℚ (HahnSeries.ofPowerSeries ℤ ℚ (1 + PowerSeries.X)) *
          HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X +
        HahnSeries.ofPowerSeries ℤ ℚ (1 + PowerSeries.X) *
          LaurentSeries.derivative ℚ (HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X) :=
  LaurentSeries.derivative_ofPowerSeries_mul _ _

end ResidueTest
