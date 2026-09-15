/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.RatFuncAtPoint
import Mathlib.Tactic

noncomputable section

open Polynomial
open AlgebraicAnalysis

namespace RatFuncAtPointTest

/-- The local expansion of `1/X` at zero has residue one. -/
example : RatFunc.residueAtPoint ℚ 0 (RatFunc.X : RatFunc ℚ)⁻¹ = 1 := by
  simp [RatFunc.residueAtPoint, LaurentSeries.residue_apply]

/-- Translation is explicit: at the point `2`, the global coordinate is the
local parameter plus the constant `2`. -/
example :
    RatFunc.atPoint ℚ 2 (RatFunc.X : RatFunc ℚ) =
      HahnSeries.C 2 + (HahnSeries.single 1 1 : LaurentSeries ℚ) := by
  exact RatFunc.atPoint_X ℚ 2

/-- Hostile derivative check: although `-1/X²` has a pole at zero, its
residue vanishes because it is a rational derivative. -/
example :
    RatFunc.residueAtPoint ℚ 0
      (RatFunc.derivative ℚ (RatFunc.X : RatFunc ℚ)⁻¹) = 0 := by
  exact RatFunc.residueAtPoint_derivative ℚ 0 _

end RatFuncAtPointTest
