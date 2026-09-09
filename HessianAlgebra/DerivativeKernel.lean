/- SPDX-License-Identifier: Apache-2.0 -/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-! The common kernel of formal partial derivatives in characteristic zero. -/
namespace HessianAlgebra
open MvPolynomial

variable {σ K : Type*} [Field K] [CharZero K]

theorem eq_constant_of_pderiv_eq_zero (f : MvPolynomial σ K)
    (h : ∀ i, pderiv i f = 0) : f = C (coeff 0 f) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d
    simp
  · have hi : ∃ i, d i ≠ 0 := by
      by_contra hn
      apply hd
      ext i
      simpa using not_exists.mp hn i
    obtain ⟨i, hi⟩ := hi
    let e := d - Finsupp.single i 1
    have he : e + Finsupp.single i 1 = d := by
      apply tsub_add_cancel_of_le
      intro j
      by_cases hj : j = i
      · subst j
        simpa using Nat.one_le_iff_ne_zero.mpr hi
      · simp [Finsupp.single_apply, hj]
    have hc := congrArg (coeff e) (h i)
    rw [coeff_pderiv, he] at hc
    have hn : (e i : K) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (e i)
    have hz : coeff d f = 0 := (mul_eq_zero.mp (by simpa using hc)).resolve_right hn
    simp [hz, hd, Ne.symm hd]

theorem eq_zero_of_pderiv_eq_zero (f : MvPolynomial σ K)
    (h : ∀ i, pderiv i f = 0) (h0 : coeff 0 f = 0) : f = 0 := by
  rw [eq_constant_of_pderiv_eq_zero f h, h0, map_zero]

end HessianAlgebra
