/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.Combinatorics.FiniteFloorSum
import Mathlib.Tactic

open scoped BigOperators

/-! Concrete consumers for finite floor-sum filtration bounds. -/

example : (∑ i ∈ ({0, 1, 2} : Finset ℕ), (i + 1) / 2) = 2 := by norm_num

example : (∑ i ∈ ({0, 1} : Finset ℕ), max 0 (3 - (2 * i + 1))) = 2 := by
  norm_num

example : (∑ i ∈ ({0, 1} : Finset ℕ), max 0 (3 - (2 * i + 1) / 2)) = 5 := by
  norm_num

example :
    ∑ i ∈ ({0, 1, 2} : Finset ℕ), (i + 1) / 2 ≤
      (∑ i ∈ ({0, 1, 2} : Finset ℕ), (i + 1)) / 2 := by
  exact Finset.sum_half_le_half_sum {0, 1, 2} (fun i => i + 1)

example :
    ∑ i ∈ ({0, 1, 2} : Finset ℕ), (2 * i + 1) / 3 ≤
      (∑ i ∈ ({0, 1, 2} : Finset ℕ), (2 * i + 1)) / 3 := by
  exact Finset.sum_div_le_div_sum {0, 1, 2} (fun i => 2 * i + 1) 3

example :
    ∑ i ∈ ({0} : Finset ℕ), (Finsupp.single 0 5 : ℕ →₀ ℕ) i / 2 ≤ 5 / 2 := by
  apply Finset.sum_half_le_of_mem_finsuppAntidiag
  simp

example : 7 - 4 + 2 * 3 ≤
    7 + (∑ i ∈ ({0, 1} : Finset ℕ), max 0 (3 - (2 * i + 1))) := by
  apply Finset.residual_exponent_lower_bound 3 7 4 {0, 1} (fun i => 2 * i + 1)
  · norm_num
  · omega

example : 4 - 4 / 2 + 2 * 3 ≤
    4 + (∑ i ∈ ({0, 1} : Finset ℕ), max 0 (3 - (2 * i + 1) / 2)) := by
  apply Finset.residual_half_exponent_lower_bound 3 4 4 {0, 1} (fun i => 2 * i + 1)
  · norm_num
  · omega
