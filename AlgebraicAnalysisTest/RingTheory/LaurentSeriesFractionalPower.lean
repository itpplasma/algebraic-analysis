/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.LaurentSeriesFractionalPower
import Mathlib.Tactic

/-! Concrete leading-term and nontrivial-binomial controls. -/

namespace AlgebraicAnalysis.LaurentSeries

noncomputable section

/-- `X²(1+X)^(-2/3)` starts in degree two with coefficient one. -/
example (z : ℤ) (hz : z < 2) :
    (monicNegativeFractionalPower (PowerSeries.X : PowerSeries ℚ) 2 3).coeff z = 0 := by
  exact monicNegativeFractionalPower_coeff_eq_zero_of_lt _ _ _ _ hz

example :
    (monicNegativeFractionalPower (PowerSeries.X : PowerSeries ℚ) 2 3).coeff 2 = 1 := by
  apply monicNegativeFractionalPower_coeff_self
  simp

/-- The first tail coefficient is genuinely fractional, so the oracle does
not reduce the construction to the leading monomial. -/
example :
    (monicNegativeFractionalPower (PowerSeries.X : PowerSeries ℚ) 2 3).coeff 3 =
      -(2 / 3 : ℚ) := by
  norm_num [monicNegativeFractionalPower, HahnSeries.coeff_single_mul,
    PowerSeries.subst_X]
  rw [show (1 : ℤ) = (1 : ℕ) by rfl,
    HahnSeries.ofPowerSeries_apply_coeff]
  simp [PowerSeries.binomialSeries_coeff]

/-- Orientation control: `X⁻³(1+X)` has consecutive unit coefficients in
degrees `-3` and `-2`. -/
example :
    (normalizedMonicSeries (PowerSeries.X : PowerSeries ℚ) 3).coeff (-3) = 1 := by
  norm_num [normalizedMonicSeries, HahnSeries.coeff_single_mul]

example :
    (normalizedMonicSeries (PowerSeries.X : PowerSeries ℚ) 3).coeff (-2) = 1 := by
  norm_num [normalizedMonicSeries, HahnSeries.coeff_single_mul]

/-- The same nontrivial row satisfies its exact algebraic root relation with
the normalized cubic Laurent series. -/
private noncomputable def cubicRoot : LaurentSeries ℚ :=
  monicNegativeFractionalPower PowerSeries.X 2 3

private noncomputable def cubicF : LaurentSeries ℚ :=
  normalizedMonicSeries PowerSeries.X 3

private theorem cubicRoot_relation : cubicRoot ^ 3 * cubicF ^ 2 = 1 := by
  exact monicNegativeFractionalPower_pow_mul_normalizedMonicSeries_pow
    PowerSeries.X (by simp) 2 3 (by norm_num)

example :
    (monicNegativeFractionalPower (PowerSeries.X : PowerSeries ℚ) 2 3) ^ 3 *
        (normalizedMonicSeries (PowerSeries.X : PowerSeries ℚ) 3) ^ 2 = 1 := by
  exact cubicRoot_relation

/-- Composition control: the concrete cubic root relation feeds the Laurent
derivative-compatibility theorem without an additional power hypothesis. -/
example :
    LaurentSeries.spectralDerivation ℤ cubicRoot *
        LaurentSeries.coefficientwiseDerivation (0 : Derivation ℤ ℚ ℚ) cubicF =
      LaurentSeries.coefficientwiseDerivation (0 : Derivation ℤ ℚ ℚ) cubicRoot *
        LaurentSeries.spectralDerivation ℤ cubicF := by
  exact monicNegativeFractionalPower_derivative_compatible
    (0 : Derivation ℤ ℚ ℚ) PowerSeries.X (by simp) 2 3 (by norm_num)

/-- For `F=X⁻³(1+X)`, the factor `(dF/ds)F^(-2/3)` starts at `X⁰`
with coefficient three. -/
example :
    (atInfinityDerivative
          (normalizedMonicSeries (PowerSeries.X : PowerSeries ℚ) 3) *
        monicNegativeFractionalPower PowerSeries.X 2 3).coeff 0 = 3 := by
  exact normalizedMomentFactor_coeff_leading PowerSeries.X (by simp) 2 3
    (by norm_num)

#print axioms AlgebraicAnalysis.LaurentSeries.monicNegativeFractionalPower_coeff_eq_zero_of_lt
#print axioms AlgebraicAnalysis.LaurentSeries.monicNegativeFractionalPower_coeff_self
#print axioms PowerSeries.subst_binomialSeries_neg_div_pow_mul_one_add_pow
#print axioms AlgebraicAnalysis.LaurentSeries.monicNegativeFractionalPower_pow_mul_normalizedMonicSeries_pow
#print axioms AlgebraicAnalysis.LaurentSeries.monicNegativeFractionalPower_derivative_compatible
#print axioms AlgebraicAnalysis.LaurentSeries.normalizedMomentFactor_coeff_leading

end

end AlgebraicAnalysis.LaurentSeries
