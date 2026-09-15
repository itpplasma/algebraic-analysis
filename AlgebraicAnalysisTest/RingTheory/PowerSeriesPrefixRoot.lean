/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.PowerSeriesPrefixRoot
import Mathlib.Tactic

/-! Concrete prefix-recovery and hostile normalization oracles. -/

open scoped PowerSeries

namespace PowerSeries

noncomputable section

private def quadratic (a : ℚ) : ℚ⟦X⟧ :=
  mk fun n ↦ if n = 0 then 1 else if n = 1 then 2 else if n = 2 then a else 0

/-- Equal square coefficients through degree two recover the quadratic
coefficient once the common nonzero normalization is fixed. -/
example (a b : ℚ)
    (hpow : ∀ i ≤ 2, coeff i (quadratic a ^ 2) =
      coeff i (quadratic b ^ 2)) : a = b := by
  have h := coeff_eq_of_pow_coeff_eq_of_le (K := 2) (n := 2)
    (by norm_num) (f := quadratic a) (g := quadratic b)
    (by simp [quadratic]) (by simp [quadratic])
    hpow 2 (by omega)
  simpa [quadratic] using h

/-- Hostile control: equal powers do not determine roots when the constant
coefficients are allowed to differ. -/
example : (C (1 : ℚ)) ^ 2 = (C (-1 : ℚ)) ^ 2 ∧
    coeff 0 (C (1 : ℚ)) ≠ coeff 0 (C (-1 : ℚ)) := by
  constructor <;> norm_num

/-- Hostile control: the nonzero normalization cannot be dropped. -/
example : (X : ℚ⟦X⟧) ^ 2 = (-X) ^ 2 ∧
    coeff 1 (X : ℚ⟦X⟧) ≠ coeff 1 (-X) := by
  constructor
  · ring
  · norm_num

end

end PowerSeries
