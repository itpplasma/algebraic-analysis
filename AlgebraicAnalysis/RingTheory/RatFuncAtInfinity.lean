/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.LaurentSeries

/-!
# Rational functions at infinity

This module constructs variable inversion on a rational function field and the induced Laurent
expansion at infinity. Its main theorem identifies the nonpositive Laurent coefficients with the
Euclidean polynomial part of the rational function.
-/

noncomputable section

open Polynomial

namespace RatFunc

variable (K : Type*) [Field K]

private def invertPolynomial : K[X] →+* K⟮X⟯ :=
  Polynomial.eval₂RingHom (algebraMap K K⟮X⟯) (RatFunc.X⁻¹)

private theorem invertPolynomial_ne_zero {p : K[X]} (hp : p ≠ 0) :
    invertPolynomial K p ≠ 0 := by
  intro h
  let _ : Invertible (RatFunc.X : K⟮X⟯) :=
    invertibleOfNonzero RatFunc.X_ne_zero
  let N := p.natDegree
  have hreflect : (p.reflect N).natDegree ≤ N := by
    simpa [N] using (Polynomial.natDegree_reflect_le (N := N) (p := p))
  have heq := (Polynomial.eval₂_reflect_eq_zero_iff
    (algebraMap K K⟮X⟯) (RatFunc.X : K⟮X⟯) N (p.reflect N) hreflect)
  have hinv : Polynomial.eval₂ (algebraMap K K⟮X⟯) (⅟(RatFunc.X : K⟮X⟯)) p = 0 := by
    simpa [invertPolynomial, N] using h
  have hmap : Polynomial.eval₂ (algebraMap K K⟮X⟯)
      (RatFunc.X : K⟮X⟯) (p.reflect N) = 0 := heq.mp (by simpa using hinv)
  rw [← Polynomial.aeval_def,
    RatFunc.aeval_X_left_eq_algebraMap] at hmap
  have hz : p.reflect N = 0 := by
    apply FaithfulSMul.algebraMap_injective K[X] K⟮X⟯
    simpa only [map_zero] using hmap
  exact hp (Polynomial.reflect_eq_zero_iff.mp hz)

private theorem invertPolynomial_injective : Function.Injective (invertPolynomial K) := by
  intro p q hpq
  apply sub_eq_zero.mp
  by_contra hp0
  exact invertPolynomial_ne_zero K hp0 (by rw [map_sub, hpq, sub_self])

/-- The involution of the rational function field obtained by sending `X` to `X⁻¹`. -/
def inversion : K⟮X⟯ →+* K⟮X⟯ :=
  RatFunc.liftRingHom (invertPolynomial K)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (invertPolynomial_injective K))

private theorem inversion_algebraMap (p : K[X]) :
    inversion K (algebraMap K[X] K⟮X⟯ p) = invertPolynomial K p := by
  exact RatFunc.liftRingHom_algebraMap _ _ _

/-- Variable inversion sends `X` to `X⁻¹`. -/
@[simp] theorem inversion_X : inversion K (RatFunc.X : K⟮X⟯) = X⁻¹ := by
  rw [inversion, RatFunc.liftRingHom_X]
  simp [invertPolynomial]

/-- Expand a rational function at infinity as a Laurent series in `X⁻¹`. -/
def atInfinity : K⟮X⟯ →+* LaurentSeries K :=
  (algebraMap K⟮X⟯ (LaurentSeries K)).comp (inversion K)

private theorem atInfinity_algebraMap (p : K[X]) :
    atInfinity K (algebraMap K[X] K⟮X⟯ p) =
      algebraMap K⟮X⟯ (LaurentSeries K) (invertPolynomial K p) := by
  change algebraMap K⟮X⟯ (LaurentSeries K)
      (inversion K (algebraMap K[X] K⟮X⟯ p)) = _
  rw [inversion_algebraMap]

/-- The expansion at infinity sends `X` to the Laurent monomial of exponent `-1`. -/
@[simp] theorem atInfinity_X :
    atInfinity K (RatFunc.X : K⟮X⟯) =
      (HahnSeries.single (-1) 1 : LaurentSeries K) := by
  simp [atInfinity]

private theorem coe_C_at_Laurent (a : K) :
    algebraMap K⟮X⟯ (LaurentSeries K) (RatFunc.C a) = HahnSeries.C a := by
  calc
    _ = (((Polynomial.C a : K[X]) : PowerSeries K) : LaurentSeries K) :=
      (RatFunc.coe_coe (Polynomial.C a)).symm
    _ = ((PowerSeries.C a : PowerSeries K) : LaurentSeries K) := by simp
    _ = HahnSeries.C a := PowerSeries.coe_C a

/-- For a polynomial, the coefficient of `X⁻ᵏ` at infinity is its coefficient of `Xᵏ`. -/
theorem coeff_atInfinity_algebraMap (p : K[X]) (k : ℕ) :
    (atInfinity K (algebraMap K[X] K⟮X⟯ p)).coeff (-(k : ℤ)) =
      p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, HahnSeries.coeff_add, hp, hq]
      rfl
  | monomial n a =>
      rw [atInfinity_algebraMap]
      simp only [invertPolynomial, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_monomial, map_mul, map_pow, map_inv₀,
        RatFunc.coe_X]
      rw [show algebraMap K⟮X⟯ (LaurentSeries K)
          (algebraMap K K⟮X⟯ a) = HahnSeries.C a by
        simpa using coe_C_at_Laurent K a]
      rw [HahnSeries.C_apply, HahnSeries.inv_single,
        HahnSeries.single_pow, HahnSeries.single_mul_single]
      rw [HahnSeries.coeff_single, Polynomial.coeff_monomial]
      by_cases hnk : n = k
      · subst k
        simp
      · have hneg : -(k : ℤ) ≠ -(n : ℤ) := by omega
        simp [hnk, hneg]

private theorem order_atInfinity_algebraMap {p : K[X]} (hp : p ≠ 0) :
    (atInfinity K (algebraMap K[X] K⟮X⟯ p)).order =
      -(p.natDegree : ℤ) := by
  let f := atInfinity K (algebraMap K[X] K⟮X⟯ p)
  have hf : f ≠ 0 := by
    intro hf0
    have hc := coeff_atInfinity_algebraMap K p p.natDegree
    change f.coeff (-(p.natDegree : ℤ)) = p.coeff p.natDegree at hc
    rw [hf0] at hc
    simp only [HahnSeries.coeff_zero] at hc
    exact (Polynomial.leadingCoeff_ne_zero.mpr hp) hc.symm
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    rw [coeff_atInfinity_algebraMap]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  · apply (HahnSeries.le_order_iff_forall hf).2
    intro z hz
    have hz0 : z ≤ 0 := by omega
    obtain ⟨s, rfl⟩ := Int.exists_eq_neg_ofNat hz0
    rw [coeff_atInfinity_algebraMap]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega

private theorem atInfinity_algebraMap_ne_zero {p : K[X]} (hp : p ≠ 0) :
    atInfinity K (algebraMap K[X] K⟮X⟯ p) ≠ 0 := by
  intro hz
  have hc := coeff_atInfinity_algebraMap K p p.natDegree
  rw [hz] at hc
  exact (Polynomial.leadingCoeff_ne_zero.mpr hp) (by simpa using hc.symm)

private theorem order_inv_of_ne_zero {x : LaurentSeries K} (hx : x ≠ 0) :
    x⁻¹.order = -x.order := by
  have h := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one] at h
  omega

private theorem order_atInfinity_div_algebraMap {p q : K[X]}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (atInfinity K
      (algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q)).order =
        (q.natDegree : ℤ) - p.natDegree := by
  have hpS := atInfinity_algebraMap_ne_zero K hp
  have hqS := atInfinity_algebraMap_ne_zero K hq
  rw [map_div₀, div_eq_mul_inv,
    HahnSeries.order_mul hpS (inv_ne_zero hqS),
    order_inv_of_ne_zero K hqS, order_atInfinity_algebraMap K hp,
    order_atInfinity_algebraMap K hq]
  ring

private theorem coeff_atInfinity_div_algebraMap_eq_zero {p q : K[X]}
    (hp : p ≠ 0) (hq : q ≠ 0) (hdeg : p.natDegree < q.natDegree)
    (k : ℕ) :
    (atInfinity K
      (algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q)).coeff
        (-(k : ℤ)) = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [order_atInfinity_div_algebraMap K hp hq]
  omega

/-- The Euclidean polynomial part of a rational function. -/
def polynomialPart (v : K⟮X⟯) : K[X] := v.num / v.denom

private theorem num_div_denom_decomposition (v : K⟮X⟯) :
    v = algebraMap K[X] K⟮X⟯ (polynomialPart K v) +
      algebraMap K[X] K⟮X⟯ (v.num % v.denom) /
        algebraMap K[X] K⟮X⟯ v.denom := by
  have hden : algebraMap K[X] K⟮X⟯ v.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero v.denom_ne_zero
  calc
    v = algebraMap K[X] K⟮X⟯ v.num /
        algebraMap K[X] K⟮X⟯ v.denom := (RatFunc.num_div_denom v).symm
    _ = _ := by
      apply (div_eq_iff hden).2
      rw [add_mul, div_mul_cancel₀ _ hden, ← map_mul, ← map_add]
      apply congr_arg (algebraMap K[X] K⟮X⟯)
      simpa [polynomialPart, mul_comm] using
        (EuclideanDomain.div_add_mod v.num v.denom).symm

/-- Nonpositive coefficients of the expansion at infinity are exactly the coefficients of the
Euclidean polynomial part. -/
theorem coeff_atInfinity_eq_polynomialPart (v : K⟮X⟯) (k : ℕ) :
    (atInfinity K v).coeff (-(k : ℤ)) = (polynomialPart K v).coeff k := by
  conv_lhs => rw [num_div_denom_decomposition (K := K) v]
  rw [map_add, HahnSeries.coeff_add, coeff_atInfinity_algebraMap]
  by_cases hrem : v.num % v.denom = 0
  · simp [hrem]
  · have hdeg : (v.num % v.denom).natDegree < v.denom.natDegree :=
      Polynomial.natDegree_lt_natDegree hrem
        (Polynomial.degree_mod_lt v.num v.denom_ne_zero)
    rw [coeff_atInfinity_div_algebraMap_eq_zero K hrem v.denom_ne_zero hdeg k,
      add_zero]

end RatFunc
