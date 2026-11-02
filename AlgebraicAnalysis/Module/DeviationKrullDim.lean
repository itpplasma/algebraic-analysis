module
public import AlgebraicAnalysis.Module.Deviation
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

/-!
# Deviation of a commutative Noetherian ring is bounded by its Krull dimension

For a commutative Noetherian ring `A` of finite Krull dimension `m`, the
lattice of ideals of `A` has Gabriel–Rentschler deviation at most `m`:
`Module.devLE_of_ringKrullDim_le`. This is the inequality
`Kdim A ≤ cl.Kdim A` of [McConnell–Robson, *Noncommutative Noetherian Rings*,
6.4.8] (equality holds there; only the upper bound is formalized here).

## Proof

* `Module.devLE_iff_small_factors` restates the deviation bound uniformly in
  terms of the strict strata `Module.Small`: `DevLE n M` iff every descending
  chain eventually has successive factors in `Small n`.
* `Module.small_of_le_annihilator`: if `Small e (A ⧸ q)` for every prime
  `q ⊇ J`, then every finitely generated module killed by `J` is in `Small e`.
  This uses Mathlib's prime filtration
  `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime` and the
  extension rule `Module.small_iff_of_exact`.
* `Module.small_quotient_prime_of_coheight_lt`: by induction on `n`, if the
  prime `p` has coheight `< n` in `PrimeSpectrum A` then `Small n (A ⧸ p)`.
  For a descending chain of ideals of `A ⧸ p` that never reaches zero, choose
  `a ∉ p` representing a nonzero element of `c (i+1)`; then `a` and `p` kill
  `c i / c (i+1)`, so every prime in its prime filtration strictly contains
  `p` and has smaller coheight.

No dimension is assigned; `Order.coheight` and `ringKrullDim` are Mathlib's.
-/

universe u v

namespace Module

section Strata

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The successive factors of a descending chain lie in the strict stratum
`Small n` from some point on exactly when the deviation is at most `n`. At
`n = 0` the factors are zero, i.e. the chain stabilizes. -/
theorem devLE_iff_small_factors (n : ℕ) : DevLE R n M ↔
    ∀ c : ℕ → Submodule R M, Antitone c → ∃ N, ∀ i, N ≤ i →
      Small R n (c i ⧸ (c (i + 1)).comap (c i).subtype) := by
  cases n with
  | succ n => exact devLE_succ_iff n
  | zero =>
    have key : ∀ (c : ℕ → Submodule R M), Antitone c → ∀ i,
        Subsingleton (c i ⧸ (c (i + 1)).comap (c i).subtype) ↔ c (i + 1) = c i := by
      intro c hc i
      rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
      exact ⟨fun h => le_antisymm (hc (Nat.le_succ i)) h, fun h => h.ge⟩
    constructor
    · intro h c hc
      obtain ⟨N, hN⟩ := h c hc
      refine ⟨N, fun i hi => (key c hc i).mpr ?_⟩
      exact (hN (i + 1) (Nat.le_succ_of_le hi)).trans (hN i hi).symm
    · intro h c hc
      obtain ⟨N, hN⟩ := h c hc
      refine ⟨N, fun i hi => ?_⟩
      induction i, hi using Nat.le_induction with
      | base => rfl
      | succ i hi ih => exact ((key c hc i).mp (hN i hi)).trans ih

end Strata

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **Prime-filtration bound.** If every quotient `A ⧸ q` by a prime `q ⊇ J`
lies in the stratum `Small e`, then so does every finitely generated module
annihilated by `J`. -/
theorem small_of_le_annihilator (e : ℕ) (J : Ideal A)
    (hJ : ∀ q : PrimeSpectrum A, J ≤ q.asIdeal → Small A e (A ⧸ q.asIdeal))
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : J ≤ Module.annihilator A M) : Small A e M := by
  revert hM
  induction ‹Module.Finite A M› using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    with
  | subsingleton N =>
    intro _
    cases e with
    | zero => exact (small_zero_iff).mpr inferInstance
    | succ e => exact devLE_of_subsingleton e
  | quotient N q f =>
    intro hN
    refine (small_linearEquiv_iff e f).mpr (hJ q fun r hr => ?_)
    have hr' : r ∈ Module.annihilator A (A ⧸ q.asIdeal) := f.annihilator_eq ▸ hN hr
    have h1 := (Module.mem_annihilator.mp hr') 1
    rwa [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem] at h1
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hN
    exact (small_iff_of_exact e f g hf hg hfg).mpr
      ⟨h₁ (hN.trans (f.annihilator_le_of_injective hf)),
        h₃ (hN.trans (g.annihilator_le_of_surjective hg))⟩

omit [IsNoetherianRing A] in
/-- In `A ⧸ p`, multiplication by a representative `a` of an element of a
submodule `C` maps every element into `C`. -/
private theorem smul_mem_of_mk_mem {p : Ideal A} (C : Submodule A (A ⧸ p)) {a : A}
    (ha : Ideal.Quotient.mk p a ∈ C) (m : A ⧸ p) : a • m ∈ C := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m
  have : a • Ideal.Quotient.mk p b = b • Ideal.Quotient.mk p a := by
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      mul_comm]
  rw [this]
  exact C.smul_mem b ha

/-- **Prime quotients.** If the prime `p` has coheight strictly below `n` in
`PrimeSpectrum A`, then the cyclic module `A ⧸ p` lies in the stratum
`Small n`, i.e. has deviation at most `n - 1`. -/
theorem small_quotient_prime_of_coheight_lt (n : ℕ) :
    ∀ p : PrimeSpectrum A, Order.coheight p < n → Small A n (A ⧸ p.asIdeal) := by
  induction n with
  | zero => intro p hp; exact absurd hp (not_lt_bot)
  | succ n ih =>
    intro p hp
    have hpn : Order.coheight p ≤ n :=
      (ENat.lt_add_one_iff (ENat.natCast_ne_top n)).mp (by exact_mod_cast hp)
    show DevLE A n (A ⧸ p.asIdeal)
    rw [devLE_iff_small_factors]
    intro c hc
    by_cases hbot : ∃ N, c N = ⊥
    · obtain ⟨N, hN⟩ := hbot
      refine ⟨N, fun i hi => ?_⟩
      have hci : c i = ⊥ := le_bot_iff.mp (hN ▸ hc hi)
      have : Subsingleton (c i) := by rw [hci]; infer_instance
      have : Subsingleton (c i ⧸ (c (i + 1)).comap (c i).subtype) :=
        Submodule.Quotient.mk_surjective _ |>.subsingleton
      cases n with
      | zero => exact (small_zero_iff).mpr inferInstance
      | succ e => exact devLE_of_subsingleton e
    push Not at hbot
    refine ⟨0, fun i _ => ?_⟩
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hbot (i + 1))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hap : a ∉ p.asIdeal := fun h => hx0 (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    set J : Ideal A := p.asIdeal ⊔ Ideal.span {a}
    apply small_of_le_annihilator n J
    · intro q hq
      have hlt : p < q := by
        refine lt_of_le_of_ne (fun r hr => hq (Ideal.mem_sup_left hr)) fun he => hap ?_
        rw [he]
        exact hq (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
      have hfin : Order.coheight q < ⊤ :=
        ((Order.coheight_anti hlt.le).trans hpn).trans_lt (ENat.natCast_lt_top n)
      exact ih q ((Order.coheight_strictAnti hlt hfin).trans_le hpn)
    · rw [sup_le_iff]
      constructor
      · intro r hr
        rw [Module.mem_annihilator]
        intro m
        obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ m
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
        have : r • Ideal.Quotient.mk p.asIdeal b = 0 := by
          rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
            Ideal.Quotient.eq_zero_iff_mem]
          exact p.asIdeal.mul_mem_right b hr
        simp only [Submodule.mem_comap, Submodule.subtype_apply, SetLike.val_smul, this]
        exact (c (i + 1)).zero_mem
      · rw [Ideal.span_le]
        rintro r (rfl : r = a)
        rw [SetLike.mem_coe, Module.mem_annihilator]
        intro m
        obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ m
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact smul_mem_of_mk_mem (c (i + 1)) hx y

/-- **[MR 6.4.8], upper bound.** A commutative Noetherian ring of Krull
dimension at most `m` has ideal lattice of deviation at most `m`. -/
theorem devLE_of_ringKrullDim_le (m : ℕ) (h : ringKrullDim A ≤ m) : DevLE A m A := by
  have hS : Small A (m + 1) A := by
    refine small_of_le_annihilator (m + 1) ⊥ (fun q _ => ?_) bot_le
    refine small_quotient_prime_of_coheight_lt (m + 1) q ?_
    have hq : (Order.coheight q : WithBot ℕ∞) ≤ m :=
      (Order.coheight_le_krullDim q).trans h
    have hq' : Order.coheight q ≤ m := by exact_mod_cast hq
    exact lt_of_le_of_lt hq' (by exact_mod_cast Nat.lt_succ_self m)
  exact hS

/-- Finite Krull dimension gives deviation at most omega. -/
theorem devLE_exists_of_ringKrullDim_ne_top (h : ringKrullDim A ≠ ⊤) :
    ∃ m : ℕ, DevLE A m A := by
  rcases hA : ringKrullDim A with _ | _ | m
  · exact ⟨0, devLE_of_ringKrullDim_le 0 (by rw [hA]; exact bot_le)⟩
  · exact absurd hA h
  · exact ⟨m, devLE_of_ringKrullDim_le m (by rw [hA]; rfl)⟩

end Module
