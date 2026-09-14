/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite sums of natural-number quotients

Reusable arithmetic for filtered convolution arguments.  The sum of termwise
natural quotients is bounded by the quotient of the sum, and the specialization
to a `finsuppAntidiag` controls floor-half filtration losses by total degree.
-/

open scoped BigOperators

namespace Finset

theorem sum_div_le_div_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) (d : ℕ) :
    ∑ i ∈ s, f i / d ≤ (∑ i ∈ s, f i) / d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact le_trans (Nat.add_le_add_left ih _) Nat.div_add_div_le_add_div

theorem sum_half_le_half_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ∑ i ∈ s, f i / 2 ≤ (∑ i ∈ s, f i) / 2 :=
  sum_div_le_div_sum s f 2

theorem sum_half_le_of_mem_finsuppAntidiag
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {n : ℕ}
    {f : ι →₀ ℕ} (hf : f ∈ s.finsuppAntidiag n) :
    ∑ i ∈ s, f i / 2 ≤ n / 2 := by
  rw [← (mem_finsuppAntidiag.mp hf).1]
  exact sum_half_le_half_sum s f

theorem sum_max_zero_sub_add_sum_min_eq
    {ι : Type*} (A : ℕ) (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, max 0 (A - f i)) + (∑ i ∈ s, min A (f i)) = s.card * A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx, Finset.card_insert_of_notMem hx]
      rw [show max 0 (A - f x) = A - min A (f x) by
        simp [tsub_eq_tsub_min]]
      calc
        A - min A (f x) + (∑ i ∈ s, max 0 (A - f i)) +
            (min A (f x) + ∑ i ∈ s, min A (f i)) =
            (A - min A (f x) + min A (f x)) +
              ((∑ i ∈ s, max 0 (A - f i)) +
                ∑ i ∈ s, min A (f i)) := by ac_rfl
        _ = A + ((∑ i ∈ s, max 0 (A - f i)) +
              ∑ i ∈ s, min A (f i)) := by
          rw [Nat.sub_add_cancel (min_le_left A (f x))]
        _ = A + s.card * A := by rw [ih]
        _ = (s.card + 1) * A := by
          simp [Nat.succ_mul, add_comm]

theorem residual_exponent_lower_bound
    {ι : Type*} (A B k : ℕ) (s : Finset ι) (f : ι → ℕ)
    (hsum : (∑ i ∈ s, f i) = k) (hk : k ≤ B) :
    B - k ≤ B + (∑ i ∈ s, max 0 (A - f i)) - s.card * A := by
  classical
  have hcomp := sum_max_zero_sub_add_sum_min_eq A s f
  have hmin : (∑ i ∈ s, min A (f i)) ≤ k := by
    rw [← hsum]
    exact Finset.sum_le_sum fun i _ => min_le_right _ _
  omega

theorem residual_half_exponent_lower_bound
    {ι : Type*} (A B k : ℕ) (s : Finset ι) (f : ι → ℕ)
    (hsum : (∑ i ∈ s, f i) = k) (hk : k ≤ 2 * B) :
    B - k / 2 ≤
      B + (∑ i ∈ s, max 0 (A - f i / 2)) - s.card * A := by
  classical
  have hsumHalf : (∑ i ∈ s, f i / 2) ≤ k / 2 := by
    apply (sum_half_le_half_sum s f).trans_eq
    rw [hsum]
  have hcomp := sum_max_zero_sub_add_sum_min_eq A s (fun i => f i / 2)
  have hmin : (∑ i ∈ s, min A (f i / 2)) ≤ k / 2 := by
    exact (Finset.sum_le_sum fun i _ => min_le_right A (f i / 2)).trans hsumHalf
  omega

end Finset
