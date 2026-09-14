import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Fixed-degree reversal of a power-series truncation

This file packages the finite coefficient reversal used when a bounded
expansion at infinity is returned to polynomial coordinates.
-/

noncomputable section

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- Reverse the first `N + 1` coefficients of a power series into a polynomial
of degree at most `N`. -/
def reverseTrunc (N : ℕ) (f : PowerSeries R) : Polynomial R :=
  (trunc (N + 1) f).reflect N

@[simp]
theorem coeff_reverseTrunc (N : ℕ) (f : PowerSeries R) (k : ℕ) :
    (reverseTrunc N f).coeff k =
      if k ≤ N then coeff (N - k) f else 0 := by
  rw [reverseTrunc, Polynomial.coeff_reflect]
  by_cases hk : k ≤ N
  · rw [Polynomial.revAt_le hk, coeff_trunc]
    have hNk : N - k < N + 1 := by omega
    simp [hNk, hk]
  · have hNk : N < k := Nat.lt_of_not_ge hk
    rw [Polynomial.revAt_eq_self_of_lt hNk, coeff_trunc]
    have hnot : ¬k < N + 1 := by omega
    simp [hk, hnot]

theorem natDegree_reverseTrunc_le (N : ℕ) (f : PowerSeries R) :
    (reverseTrunc N f).natDegree ≤ N := by
  apply Polynomial.natDegree_le_of_degree_le
  apply Polynomial.degree_le_of_natDegree_le
  calc
    (reverseTrunc N f).natDegree ≤ max N (trunc (N + 1) f).natDegree :=
      Polynomial.natDegree_reflect_le
    _ ≤ N := by
      apply max_le
      · exact le_rfl
      · have h := natDegree_trunc_lt f N
        omega

theorem degree_reverseTrunc_le (N : ℕ) (f : PowerSeries R) :
    (reverseTrunc N f).degree ≤ (N : WithBot ℕ) :=
  Polynomial.degree_le_of_natDegree_le (natDegree_reverseTrunc_le N f)

end PowerSeries
