module
public import AlgebraicAnalysis.DifferentialOperators.OrderFiltration
public import Mathlib.RingTheory.Localization.Defs

@[expose] public section

/-!
# Differential operators on a localization are determined on the base

Let `B = S⁻¹A` be a localization of the commutative ring `A`, with `B` a
`k`-algebra (no compatibility of `k` with `A` is needed). A
differential operator of finite order on `B` is determined by its values on
the image of `A` (`eq_of_forall_algebraMap_eq`).

## Proof

Induction on the order. If `P` has order zero, `P` is multiplication by
`P(1)`. Otherwise, for `a' ∈ A` the commutator `[P, a']` has lower order and
also vanishes on `A`, hence is zero; then for `b = a/s`,
`0 = P(a) = P(s b) = s P(b) + [P, s] b = s P(b)` and `s` is a unit.

This is the uniqueness half of the localization of differential operators
(Grothendieck, [EGA IV, 16.4.14]); existence for derivations is
`LocalizedPolynomialDerivations.extendDerivation`. AA-native.
-/

namespace AlgebraicAnalysis.DifferentialOperators

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k B] [Algebra A B]
  (S : Submonoid A) [IsLocalization S B]

include S in
/-- An operator of finite order on `S⁻¹A` which vanishes on the image of `A`
is zero. -/
theorem eq_zero_of_forall_algebraMap_eq_zero :
    ∀ n, ∀ P ∈ order (k := k) (R := B) n, (∀ a : A, P (algebraMap A B a) = 0) → P = 0 := by
  intro n
  induction n with
  | zero =>
      intro P hP h
      rw [(mem_order_zero_iff_eq_multiplication P).mp hP, ← map_one (algebraMap A B), h 1]
      ext
      simp
  | succ n ih =>
      intro P hP h
      have hc : ∀ a' : A, commutator P (algebraMap A B a') = 0 := fun a' =>
        ih _ ((mem_order_succ_iff P n).mp hP _) fun a => by
          rw [commutator_apply, ← map_mul, h, h, mul_zero, sub_zero]
      ext b
      obtain ⟨⟨a, s⟩, hbs⟩ := IsLocalization.surj S b
      have h1 := LinearMap.congr_fun (hc s) b
      rw [commutator_apply, mul_comm, hbs, h, LinearMap.zero_apply, zero_sub, neg_eq_zero] at h1
      exact (IsLocalization.map_units B s).mul_right_eq_zero.mp h1

include S in
/-- **Differential operators on `S⁻¹A` are determined on `A`.** Two operators of
order at most `n` on `S⁻¹A` which agree on the image of `A` are equal. -/
theorem eq_of_forall_algebraMap_eq {n : ℕ} {P Q : End (k := k) (R := B)}
    (hP : P ∈ order n) (hQ : Q ∈ order n) (h : ∀ a : A, P (algebraMap A B a) = Q (algebraMap A B a)) :
    P = Q :=
  sub_eq_zero.mp (eq_zero_of_forall_algebraMap_eq_zero S n _ (sub_mem hP hQ) fun a => by
    rw [LinearMap.sub_apply, h, sub_self])

end AlgebraicAnalysis.DifferentialOperators
