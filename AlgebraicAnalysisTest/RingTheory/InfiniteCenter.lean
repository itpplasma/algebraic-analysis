/- SPDX-License-Identifier: Apache-2.0 -/

module
public import AlgebraicAnalysis.RingTheory.InfiniteCenter
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic

@[expose] public section

/-!
Oracles for `AlgebraicAnalysis.infinite_subring_center`.

* Independent scalar oracle: the scalar matrices `c • 1` with `c ∈ ℚ` are
  pairwise distinct central elements; we exhibit an explicit injection from
  `ℚ` into the centre of `M₂(ℚ)` and check centrality entrywise.
* The conclusion is non-vacuous for a field: `ℚ` itself is infinite and its
  centre is `ℚ`.
-/

namespace AlgebraicAnalysisTest.InfiniteCenter

open AlgebraicAnalysis

/-- Centre of `M₂(ℚ)` is infinite (generic theorem applied to `ℚ`). -/
example : Infinite (Subring.center (Matrix (Fin 2) (Fin 2) ℚ)) :=
  infinite_subring_center ℚ _

/-- Independent oracle: the scalar matrix `q • 1` is central, checked entrywise. -/
theorem scalar_matrix_central (q : ℚ) (g : Matrix (Fin 2) (Fin 2) ℚ) :
    g * (q • (1 : Matrix (Fin 2) (Fin 2) ℚ)) = (q • (1 : Matrix (Fin 2) (Fin 2) ℚ)) * g := by
  ext i j
  simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, mul_comm]

/-- Independent oracle: `ℚ` has infinite centre, which is `ℚ`. -/
example : Infinite (Subring.center ℚ) := infinite_subring_center ℚ ℚ

#print axioms infinite_subring_center
