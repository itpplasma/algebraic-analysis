/- SPDX-License-Identifier: Apache-2.0 -/

module
public import AlgebraicAnalysis.Filtration.Opposite
public import AlgebraicAnalysisTest.Filtration.SymbolNoetherian
public import AlgebraicAnalysisTest.Deviation

@[expose] public section

/-!
Oracles for the opposite filtration and opposite symbol.

* Commutative oracle: `ℤᵐᵒᵖ` is `ℤ` (as rings, via `MulOpposite.unop`), so the
  right deviation of `ℤᵐᵒᵖ` must be exactly the commutative bound one. The
  upper bound uses Mathlib's Krull-dimension theory (`ringKrullDim ℤ = 1`), and
  the sharpness uses the independent Artinian argument `int_not_devLE_zero`.
* Symbol oracle: the opposite of the degree-symbol of `ℚ[X₀, X₁]` takes the
  explicit value `X₀` on `op (X₀ + 1)` in degree one, the value the un-opposed
  symbol takes on `X₀ + 1` in the existing oracle.
* Noetherian oracle: the right side of `ℚ[X₀, X₁]ᵐᵒᵖ` is Noetherian by Hilbert's
  basis theorem, which is Mathlib's instance and independent of the symbol.
-/

namespace AlgebraicAnalysisTest.Opposite

open AlgebraicAnalysis AlgebraicAnalysis.RingFiltration MvPolynomial DirectSum
open MulOpposite AlgebraicAnalysisTest.SymbolNoetherian

/-! ## Ideal correspondence oracles -/

/-- The right deviation of `ℤᵐᵒᵖ` is at most one: transported from `ℤ`. -/
theorem int_op_right_devLE_one : Module.DevLE ℤᵐᵒᵖᵐᵒᵖ 1 ℤᵐᵒᵖ :=
  (devLE_right_op_iff ℤ 1).mpr
    (Module.devLE_of_ringKrullDim_le 1 (by rw [int_ringKrullDim]; rfl))

/-- Sharpness transported to `ℤᵐᵒᵖ`: its right deviation is not zero. -/
theorem int_op_right_not_devLE_zero : ¬Module.DevLE ℤᵐᵒᵖᵐᵒᵖ 0 ℤᵐᵒᵖ :=
  fun h => AlgebraicAnalysisTest.Deviation.int_not_devLE_zero ((devLE_right_op_iff ℤ 0).mp h)

/-! ## Opposite symbol oracle -/

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-one symbol of `X₀ + 1` in the un-opposed filtration. -/
theorem grAt_one_X_add_one : S₂.grAt 1 (X 0 + 1 : MvPolynomial (Fin 2) ℚ) = X 0 := by
  rw [GradedSymbol.grAt_of_mem _ X_add_one_mem]
  change (decompose (homogeneousSubmodule (Fin 2) ℚ) (X 0 + 1) 1 : MvPolynomial (Fin 2) ℚ) = _
  rw [decompose_add, DirectSum.add_apply, Submodule.coe_add,
    decompose_of_mem_same _ ((mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℚ 0)),
    decompose_of_mem_ne _ ((mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_one _ ℚ))
      (by norm_num), add_zero]

/-- The opposite symbol of `op (X₀ + 1)` in degree one is `X₀`: the same value as the
un-opposed symbol of `X₀ + 1`, computed independently. -/
theorem opposite_grAt_one : S₂.opposite.grAt 1 (op (X 0 + 1 : MvPolynomial (Fin 2) ℚ)) = X 0 := by
  rw [GradedSymbol.grAt_opposite, grAt_one_X_add_one]

/-- The opposite filtration contains `op (X₀ + 1)` in degree one. -/
theorem op_X_add_one_mem :
    op (X 0 + 1 : MvPolynomial (Fin 2) ℚ) ∈
      ((RingFiltration.ofGradedAlgebra (homogeneousSubmodule (Fin 2) ℚ)).opposite).F 1 :=
  mem_opposite_op_iff.mpr X_add_one_mem

/-- Transport of Noetherianity: the left side of `ℚ[X₀, X₁]` is Noetherian, obtained
from the symbol of the opposite (Hilbert's basis theorem gives the same instance). -/
example : IsNoetherianRing (MvPolynomial (Fin 2) ℚ) :=
  S₂.isNoetherianRing_of_opposite_right

#print axioms int_op_right_devLE_one
#print axioms int_op_right_not_devLE_zero
#print axioms opposite_grAt_one
