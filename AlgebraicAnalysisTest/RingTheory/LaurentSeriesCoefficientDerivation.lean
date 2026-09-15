/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.LaurentSeriesCoefficientDerivation
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Tactic

/-! Concrete coefficient, residue, and commutation oracles. -/

open Polynomial
namespace AlgebraicAnalysis.LaurentSeries

noncomputable section

private def sample : LaurentSeries (Polynomial ℚ) :=
  HahnSeries.single (-1) (X ^ 2) + HahnSeries.single 2 (3 * X)

/-- The spectral derivation shifts a negative Laurent exponent and multiplies
by the original exponent. -/
example :
    (spectralDerivation ℚ (K := ℚ) (HahnSeries.single (-2) 3)).coeff (-3) = -6 := by
  norm_num [spectralDerivation_apply, _root_.LaurentSeries.derivative_apply]

/-- The coefficient derivation changes coefficients but preserves Laurent
exponents, including the residue exponent. -/
example :
    (coefficientwiseDerivation (Polynomial.derivative' (R := ℚ)) sample).coeff (-1) =
      2 * X := by
  rw [coefficientwiseDerivation_apply_coeff]
  simp [sample, Polynomial.derivative']

/-- API oracle: residue commutation is exposed in the orientation needed by a
downstream moment derivative. -/
example {K : Type*} [Field K] [Algebra ℚ K]
    (D : Derivation ℚ K K) (f : LaurentSeries K) :
    residue (coefficientwiseDerivation D f) = D (residue f) := by
  exact (coefficientwiseDerivation_residue D f).symm

/-- The concrete coefficient-field and spectral derivatives commute. -/
example :
    _root_.LaurentSeries.derivative (Polynomial ℚ)
        (coefficientwiseDerivation (Polynomial.derivative' (R := ℚ)) sample) =
      coefficientwiseDerivation (Polynomial.derivative' (R := ℚ))
        (_root_.LaurentSeries.derivative (Polynomial ℚ) sample) := by
  exact derivative_coefficientwiseDerivation_commute _ _

private def infinitySample : LaurentSeries ℚ :=
  HahnSeries.single 1 7 + HahnSeries.single (-1) 11

/-- Hostile orientation control: paper residue at `s = ∞` is `[X¹]` for
`X = s⁻¹`, not the ordinary Laurent coefficient `[X⁻¹]`. -/
example : residueAtInfinity infinitySample = 7 := by
  norm_num [residueAtInfinity_apply, infinitySample]

example : residue infinitySample = 11 := by
  norm_num [residue_apply, infinitySample]

/-- Under `d/ds = -X² d/dX`, `3X⁻²` maps to `6X⁻¹`. -/
example :
    (atInfinityDerivative (HahnSeries.single (-2) (3 : ℚ))).coeff (-1) = 6 := by
  norm_num [atInfinityDerivative_apply, HahnSeries.coeff_single_mul,
    _root_.LaurentSeries.derivative_apply,
    _root_.LaurentSeries.hasseDeriv_coeff]

example (f : LaurentSeries ℚ) :
    residueAtInfinity (atInfinityDerivative f) = 0 := by
  exact residueAtInfinity_atInfinityDerivative f

private def modeSample : LaurentSeries ℚ := HahnSeries.single 1 1

/-- API oracle for the mode-residue range, on the nonconstant unit `X`. -/
example :
    residueAtInfinity
      (modeSample ^ 0 * atInfinityDerivative (modeSample ^ 2) *
        (modeSample⁻¹) ^ 1) = 0 := by
  exact residueAtInfinity_mode_mul_eq_zero modeSample
    (by simp [modeSample]) 2 0 1 (by omega)

/-- Independent oracle: expand the same mode coefficientwise, without the
mode-residue theorem. -/
example :
    residueAtInfinity
      (modeSample ^ 0 * atInfinityDerivative (modeSample ^ 2) *
        (modeSample⁻¹) ^ 1) = 0 := by
  norm_num [modeSample, residueAtInfinity_apply,
    atInfinityDerivative_apply, HahnSeries.coeff_single_mul,
    _root_.LaurentSeries.derivative_apply,
    _root_.LaurentSeries.hasseDeriv_coeff]

example {K : Type*} [Field K] [Algebra ℚ K]
    (D : Derivation ℚ K K) (f : LaurentSeries K) :
    atInfinityDerivative (coefficientwiseDerivation D f) =
      coefficientwiseDerivation D (atInfinityDerivative f) := by
  exact atInfinityDerivative_coefficientwiseDerivation_commute D f

#print axioms AlgebraicAnalysis.LaurentSeries.coefficientwiseDerivation_apply_coeff
#print axioms AlgebraicAnalysis.LaurentSeries.derivative_coefficientwiseDerivation_commute
#print axioms AlgebraicAnalysis.LaurentSeries.coefficientwiseDerivation_residue
#print axioms AlgebraicAnalysis.LaurentSeries.derivative_mul
#print axioms AlgebraicAnalysis.LaurentSeries.spectralDerivation
#print axioms AlgebraicAnalysis.LaurentSeries.spectralDerivation_apply
#print axioms AlgebraicAnalysis.LaurentSeries.atInfinityDerivative
#print axioms AlgebraicAnalysis.LaurentSeries.atInfinityDerivative_mul
#print axioms AlgebraicAnalysis.LaurentSeries.atInfinityDerivative_pow
#print axioms AlgebraicAnalysis.LaurentSeries.residueAtInfinity_atInfinityDerivative
#print axioms AlgebraicAnalysis.LaurentSeries.residueAtInfinity_mode_mul_eq_zero
#print axioms AlgebraicAnalysis.LaurentSeries.atInfinityDerivative_coefficientwiseDerivation_commute
#print axioms AlgebraicAnalysis.LaurentSeries.coefficientwiseDerivation_residueAtInfinity

end

end AlgebraicAnalysis.LaurentSeries
