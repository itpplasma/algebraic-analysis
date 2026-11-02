module
public import AlgebraicAnalysis.DifferentialOperators.CoordinateSymbol
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section

/-!
# `D_k(R)` is a domain when `R` is a domain

Let `k` be a field of characteristic zero and `R` a commutative `k`-algebra
which is a domain. Then the ring `D_k(R)` of finite-order differential
operators is a domain (`DifferentialOperators.isDomain`). No finiteness,
smoothness or coordinate hypothesis is needed.

## Proof: polarization of the principal symbol

Write `ad_b P = [P, b] = P b - b P`. The maps `ad_b` commute pairwise, are
additive in `b`, and satisfy the Leibniz rule
`ad_b (P Q) = P ad_b Q + (ad_b P) Q` (`commutatorMap_mul`), hence
`ad_b^N (P Q) = ∑ (N choose i) ad_b^i P · ad_b^{N-i} Q`
(`commutatorMap_pow_mul`). If `P` has order at most `m`, then `ad_b^m P` is
multiplication by an element `σ_P(b) ∈ R`, the principal symbol of `P`
evaluated on `db`.

1. If `P` has exact order `m`, then `σ_P(b) ≠ 0` for some `b`
   (`exists_symbol_ne_zero`). By induction: some `ad_c P` has exact order
   `m - 1`, so `σ_{ad_c P}(b) ≠ 0` for some `b`; the value `σ_P(b + t c)` is a
   polynomial in `t ∈ k` (`exists_polynomial_symbol`, binomial theorem for the
   commuting `ad_b`, `ad_c`) whose `t`-coefficient is `m σ_{ad_c P}(b) ≠ 0`.
   A nonzero polynomial over the domain `R` has finitely many roots and `k` is
   infinite.
2. If `P`, `Q` have exact orders `m`, `n`, then
   `ad_b^{m+n} (P Q) = (m+n choose m) ad_b^m P · ad_b^n Q`, which is
   multiplication by `(m+n choose m) σ_P(b) σ_Q(b)`. Choosing `b` on a line
   through points where `σ_P` and `σ_Q` do not vanish makes both nonzero at
   once, again since a nonzero polynomial has finitely many roots. Hence
   `P Q ≠ 0`.

This is the classical fact that the principal symbol is multiplicative and
`gr D_k(R)` embeds into polynomial functions on `Ω_{R/k}`; compare
[McConnell–Robson, *Noncommutative Noetherian Rings*, 15.5.5]. The
polarization argument is AA-native.
-/

namespace AlgebraicAnalysis.DifferentialOperators

open Polynomial

section General

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- `ad_b : P ↦ [P, b] = P b - b P`, as a `k`-linear endomorphism of `End_k(R)`. -/
def commutatorMap (b : R) : End (k := k) (R := R) →ₗ[k] End (k := k) (R := R) where
  toFun P := commutator P b
  map_add' P Q := commutator_add P Q b
  map_smul' c P := commutator_smul c P b

@[simp] theorem commutatorMap_apply (b : R) (P : End (k := k) (R := R)) :
    commutatorMap b P = commutator P b := rfl

theorem commutatorMap_add (b c : R) :
    commutatorMap (k := k) (b + c) = commutatorMap b + commutatorMap c := by
  ext P y
  simp [commutator_apply, add_mul]
  abel

theorem commutatorMap_smul (t : k) (c : R) :
    commutatorMap (k := k) (t • c) = t • commutatorMap c := by
  ext P y
  simp [commutator_apply, smul_sub]

theorem commutatorMap_commute (b c : R) :
    Commute (commutatorMap (k := k) (R := R) b) (commutatorMap c) := by
  ext P y
  simp only [Module.End.mul_apply, commutatorMap_apply]
  rw [commutator_commutator_comm]

/-- Leibniz rule: `ad_b (P Q) = P ad_b Q + (ad_b P) Q`. -/
theorem commutatorMap_mul (b : R) (P Q : End (k := k) (R := R)) :
    commutatorMap b (P * Q) = P * commutatorMap b Q + commutatorMap b P * Q :=
  commutator_mul P Q b

/-- General Leibniz rule:
`ad_b^N (P Q) = ∑_{i + j = N} (N choose i) ad_b^i P · ad_b^j Q`. -/
theorem commutatorMap_pow_mul (b : R) (P Q : End (k := k) (R := R)) (N : ℕ) :
    (commutatorMap b ^ N) (P * Q) = ∑ ij ∈ Finset.antidiagonal N,
      N.choose ij.1 • ((commutatorMap b ^ ij.1) P * (commutatorMap b ^ ij.2) Q) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_antidiagonal_choose_succ_nsmul
        (fun i j => (commutatorMap b ^ i) P * (commutatorMap b ^ j) Q) N,
        pow_succ', Module.End.mul_apply, ih, map_sum]
      simp only [map_nsmul, commutatorMap_mul, smul_add, Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun ij _ => ?_
        rw [pow_succ', Module.End.mul_apply]
      · refine Finset.sum_congr rfl fun ij hij => ?_
        rw [Finset.mem_antidiagonal] at hij
        rw [← Nat.choose_symm_of_eq_add hij.symm, pow_succ', Module.End.mul_apply]

/-- `ad_b^j` lowers the order by `j`. -/
theorem commutatorMap_pow_mem_order (b : R) :
    ∀ j m, ∀ P ∈ order (k := k) (R := R) (m + j), (commutatorMap b ^ j) P ∈ order m := by
  intro j
  induction j with
  | zero => intro m P hP; simpa using hP
  | succ j ih =>
      intro m P hP
      rw [pow_succ, Module.End.mul_apply]
      exact ih m _ ((mem_order_succ_iff P (m + j)).mp (by rwa [← Nat.add_assoc] at hP) b)

/-- `ad_b^{m+1}` kills operators of order at most `m`. -/
theorem commutatorMap_pow_eq_zero (b : R) {m : ℕ} {P : End (k := k) (R := R)}
    (hP : P ∈ order m) : (commutatorMap b ^ (m + 1)) P = 0 := by
  rw [pow_succ', Module.End.mul_apply]
  exact (commutatorMap_pow_mem_order b m 0 P (by simpa using hP)) b

/-- `ad_b^j` kills operators of order less than `j`. -/
theorem commutatorMap_pow_eq_zero_of_lt (b : R) {m j : ℕ} (hmj : m < j)
    {P : End (k := k) (R := R)} (hP : P ∈ order m) : (commutatorMap b ^ j) P = 0 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hmj
  rw [show m + l + 1 = l + (m + 1) by omega, pow_add, Module.End.mul_apply,
    commutatorMap_pow_eq_zero b hP, map_zero]

/-- **The symbol is multiplicative.** If `P` has order at most `m` and `Q` order
at most `n`, then `ad_b^{m+n} (P Q) = (m+n choose m) ad_b^m P · ad_b^n Q`. -/
theorem commutatorMap_pow_mul_of_mem_order (b : R) {m n : ℕ} {P Q : End (k := k) (R := R)}
    (hP : P ∈ order m) (hQ : Q ∈ order n) :
    (commutatorMap b ^ (m + n)) (P * Q) =
      (m + n).choose m • ((commutatorMap b ^ m) P * (commutatorMap b ^ n) Q) := by
  rw [commutatorMap_pow_mul, Finset.sum_eq_single (m, n)]
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    rcases lt_or_ge m i with hi | hi
    · rw [commutatorMap_pow_eq_zero_of_lt b hi hP, zero_mul, smul_zero]
    · have hj : n < j := by
        rcases hi.lt_or_eq with hi | rfl
        · omega
        · exact absurd (by simp_all) hne
      rw [commutatorMap_pow_eq_zero_of_lt b hj hQ, mul_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (rfl : m + n = m + n)) h

/-- The value at `1` of an order-zero operator determines it. -/
theorem apply_mul_of_mem_order_zero {P : End (k := k) (R := R)} (hP : P ∈ order 0) (y : R) :
    P y = P 1 * y := by
  rw [(mem_order_zero_iff_eq_multiplication P).mp hP]
  simp [mul_comm]

/-- **Symbols along a line are polynomial.** If `P` has order at most `m`, there
is a polynomial `g ∈ R[T]` with `σ_P(b + t c) = g(t)` for all `t ∈ k`, whose
constant coefficient is `σ_P(b)` and whose linear coefficient is
`m σ_{ad_c P}(b)`, where `σ_P(b) = (ad_b^m P)(1)`. -/
theorem exists_polynomial_symbol {m : ℕ} {P : End (k := k) (R := R)} (hP : P ∈ order m)
    (b c : R) : ∃ g : R[X], (∀ t : k,
      (commutatorMap (b + t • c) ^ m) P 1 = g.eval (algebraMap k R t)) ∧
      g.coeff 0 = (commutatorMap b ^ m) P 1 ∧
      (∀ n, m = n + 1 → g.coeff 1 = (m : R) * (commutatorMap b ^ n) (commutatorMap c P) 1) := by
  classical
  let e : ℕ → R := fun i => m.choose i *
    ((commutatorMap c ^ i * commutatorMap b ^ (m - i) :
      Module.End k (End (k := k) (R := R))) P) 1
  refine ⟨∑ i ∈ Finset.range (m + 1), C (e i) * X ^ i, fun t => ?_, ?_, fun n hn => ?_⟩
  · have hc : Commute (t • commutatorMap (k := k) (R := R) c) (commutatorMap b) :=
      (commutatorMap_commute c b).smul_left t
    rw [commutatorMap_add, commutatorMap_smul, add_comm, hc.add_pow, LinearMap.sum_apply,
      LinearMap.sum_apply, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hn : ((commutatorMap c ^ i * commutatorMap b ^ (m - i) *
        ((m.choose i : ℕ) : Module.End k (End (k := k) (R := R))) :
          Module.End k (End (k := k) (R := R))) P) =
        m.choose i • ((commutatorMap c ^ i * commutatorMap b ^ (m - i) :
          Module.End k (End (k := k) (R := R))) P) := by
      rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
    rw [smul_pow, smul_mul_assoc, smul_mul_assoc, LinearMap.smul_apply, LinearMap.smul_apply, hn,
      LinearMap.smul_apply]
    simp only [eval_mul, eval_C, eval_pow, eval_X, e, nsmul_eq_mul]
    rw [Algebra.smul_def, map_pow]
    ring
  · rw [finsetSum_coeff, Finset.sum_eq_single 0]
    · simp [e]
    · intro i _ hi
      simp only [coeff_C_mul, coeff_X_pow]
      rw [ite_eq_right_iff.mpr fun h => absurd h.symm hi, mul_zero]
    · simp
  · rw [finsetSum_coeff, Finset.sum_eq_single 1]
    · subst hn
      simp only [coeff_C_mul, e, Nat.choose_one_right, Nat.add_sub_cancel, pow_one, coeff_X_one,
        mul_one]
      rw [((commutatorMap_commute c b).pow_right n).eq, Module.End.mul_apply]
    · intro i _ hi
      simp [coeff_X_pow, Ne.symm hi]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h

end General

section Domain

/-- Positive integers are nonzero in a nontrivial algebra over a field of
characteristic zero. -/
theorem natCast_ne_zero_of_charZero (k : Type*) {R : Type*} [Field k] [CharZero k] [CommRing R]
    [Nontrivial R] [Algebra k R] (n : ℕ) (hn : n ≠ 0) : (n : R) ≠ 0 := by
  rw [← map_natCast (algebraMap k R)]
  exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hn)


variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]

/-- A nonzero polynomial over `R` does not vanish at some point of `k`. -/
theorem exists_eval_algebraMap_ne_zero {g : R[X]} (hg : g ≠ 0) :
    ∃ t : k, g.eval (algebraMap k R t) ≠ 0 := by
  by_contra h
  push Not at h
  have : Infinite k := CharZero.infinite k
  refine hg (eq_zero_of_infinite_isRoot g
    ((Set.infinite_range_of_injective (algebraMap k R).injective).mono ?_))
  rintro _ ⟨t, rfl⟩
  exact h t

/-- **Nonvanishing of the symbol.** If `P` has order at most `m` but does not lie
in `orderBelow m` (exact order `m`), then `(ad_b^m P)(1) ≠ 0` for some `b`. -/
theorem exists_symbol_ne_zero :
    ∀ m, ∀ P ∈ order (k := k) (R := R) m, P ∉ orderBelow m →
      ∃ b : R, (commutatorMap b ^ m) P 1 ≠ 0 := by
  intro m
  induction m with
  | zero =>
      intro P hP hP0
      refine ⟨0, fun h => hP0 ?_⟩
      rw [orderBelow_zero, Submodule.mem_bot]
      ext y
      rw [apply_mul_of_mem_order_zero hP, show P 1 = 0 by simpa using h, zero_mul,
        LinearMap.zero_apply]
  | succ n ih =>
      intro P hP hPn
      obtain ⟨c, hc⟩ : ∃ c, commutator P c ∉ orderBelow n := by
        by_contra h
        push Not at h
        exact hPn (mem_order_iff_commutator_mem_orderBelow.mpr h)
      obtain ⟨b, hb⟩ := ih _ ((mem_order_succ_iff P n).mp hP c) hc
      obtain ⟨g, hg, -, hg1⟩ := exists_polynomial_symbol (k := k) hP b c
      have hg0 : g ≠ 0 := by
        intro h0
        have h1 := hg1 n rfl
        rw [h0, coeff_zero] at h1
        exact mul_ne_zero (natCast_ne_zero_of_charZero k _ (Nat.succ_ne_zero n)) hb h1.symm
      obtain ⟨t, ht⟩ := exists_eval_algebraMap_ne_zero (k := k) hg0
      exact ⟨b + t • c, by rwa [hg]⟩

omit [CharZero k] [IsDomain R] in
/-- Every nonzero operator has an exact order. -/
theorem exists_exact_order {P : End (k := k) (R := R)} (hP : P ∈ algebra (k := k) (R := R))
    (hP0 : P ≠ 0) : ∃ m, P ∈ order m ∧ P ∉ orderBelow m := by
  classical
  refine ⟨Nat.find hP, Nat.find_spec hP, ?_⟩
  rcases h : Nat.find hP with _ | m
  · simpa using hP0
  · exact Nat.find_min hP (by omega)

/-- **A product of nonzero differential operators is nonzero** over a domain in
characteristic zero. -/
theorem mul_ne_zero_of_mem_algebra {P Q : End (k := k) (R := R)}
    (hP : P ∈ algebra (k := k) (R := R)) (hQ : Q ∈ algebra (k := k) (R := R))
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) : P * Q ≠ 0 := by
  obtain ⟨m, hPm, hPm'⟩ := exists_exact_order hP hP0
  obtain ⟨n, hQn, hQn'⟩ := exists_exact_order hQ hQ0
  obtain ⟨b, hb⟩ := exists_symbol_ne_zero m P hPm hPm'
  obtain ⟨b', hb'⟩ := exists_symbol_ne_zero n Q hQn hQn'
  obtain ⟨gP, hgP, hgP0, -⟩ := exists_polynomial_symbol (k := k) hPm b (b' - b)
  obtain ⟨gQ, hgQ, -, -⟩ := exists_polynomial_symbol (k := k) hQn b (b' - b)
  have hP' : gP ≠ 0 := fun h => hb (by rw [← hgP0, h, coeff_zero])
  have hQ' : gQ ≠ 0 := fun h => hb' (by
    have := hgQ 1
    rw [one_smul, add_sub_cancel, h, eval_zero] at this
    exact this)
  obtain ⟨t, ht⟩ := exists_eval_algebraMap_ne_zero (k := k) (mul_ne_zero hP' hQ')
  rw [eval_mul, ← hgP, ← hgQ] at ht
  set b'' := b + t • (b' - b)
  intro hPQ
  have h := commutatorMap_pow_mul_of_mem_order (k := k) b'' hPm hQn
  rw [hPQ, map_zero] at h
  have h1 := LinearMap.congr_fun h 1
  rw [LinearMap.zero_apply, LinearMap.smul_apply, Module.End.mul_apply,
    apply_mul_of_mem_order_zero (commutatorMap_pow_mem_order b'' m 0 P (by simpa using hPm)),
    nsmul_eq_mul] at h1
  exact mul_ne_zero (natCast_ne_zero_of_charZero k _ (Nat.choose_pos (Nat.le_add_right m n)).ne') ht
    h1.symm

/-- **`D_k(R)` is a domain** whenever `R` is a domain and `k` is a field of
characteristic zero. -/
theorem isDomain : IsDomain (algebra (k := k) (R := R)) := by
  have : NoZeroDivisors (algebra (k := k) (R := R)) := ⟨fun {P Q} h => by
    by_contra hne
    push Not at hne
    exact mul_ne_zero_of_mem_algebra P.2 Q.2 (fun h0 => hne.1 (Subtype.ext h0))
      (fun h0 => hne.2 (Subtype.ext h0)) (congrArg Subtype.val h)⟩
  exact NoZeroDivisors.to_isDomain (algebra (k := k) (R := R))

end Domain

end AlgebraicAnalysis.DifferentialOperators
