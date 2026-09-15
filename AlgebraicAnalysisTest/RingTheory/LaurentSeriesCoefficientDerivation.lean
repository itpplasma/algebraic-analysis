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

#print axioms AlgebraicAnalysis.LaurentSeries.coefficientwiseDerivation_apply_coeff
#print axioms AlgebraicAnalysis.LaurentSeries.derivative_coefficientwiseDerivation_commute
#print axioms AlgebraicAnalysis.LaurentSeries.coefficientwiseDerivation_residue
#print axioms AlgebraicAnalysis.LaurentSeries.derivative_mul
#print axioms AlgebraicAnalysis.LaurentSeries.spectralDerivation
#print axioms AlgebraicAnalysis.LaurentSeries.spectralDerivation_apply

end

end AlgebraicAnalysis.LaurentSeries
