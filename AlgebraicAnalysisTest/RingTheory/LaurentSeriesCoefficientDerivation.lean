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

end

end AlgebraicAnalysis.LaurentSeries
