/- SPDX-License-Identifier: Apache-2.0 -/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Good filtrations on modules over a filtered ring

Let `R` be a commutative base ring, `A` an `R`-algebra (not assumed
commutative) and `M` a left `A`-module which is also an `R`-module with
`IsScalarTower R A M`.  A *ring filtration* of `A` is a family
`F : ℕ → Submodule R A`.  This file deliberately does **not** import a
filtered-ring structure: the four defining ring-filtration conditions

* `Monotone F`,
* `(1 : A) ∈ F 0`,
* `F i * F j ≤ F (i + j)`,
* `⨆ i, F i = ⊤`,

are carried as explicit hypotheses of each statement, and only the ones that
are actually used appear.  A separate filtered-ring file can later be
reconciled with this one by discharging exactly these hypotheses.

The module-side notions are:

* `IsCompatible F G`: `G : ℕ → Submodule R M` is ascending, exhaustive, and
  satisfies `F i • G j ≤ G (i + j)`.
* `IsGood F G`: there are an index `d` and a finite set `s` with
  `G d = F 0 • span R s`, and the filtration stabilises past `d` in the sense
  that `G (d + i) = F i • G d` for all `i`.

The stabilisation clause is stated at the single index `d`.  The apparently
stronger form `G (i + j) = F i • G j` for all `j ≥ d` is proved in
`IsGood.exists_smul_eq` under the extra hypothesis `F (i + j) ≤ F i * F j`,
which says that the ring filtration is multiplicatively generated; without
that hypothesis the two forms genuinely differ.

Main results:

* `isCompatible_generated` / `isGood_generated`: the filtration
  `n ↦ F n • span R s` attached to a finite generating set `s` of `M` is
  compatible and good, so every finitely generated `A`-module carries a good
  filtration (`exists_isGood_of_finite`).
* `exists_shift_le` and `exists_shift_le_and_le`: any good filtration is
  squeezed inside a fixed shift of any compatible filtration, hence any two
  good filtrations on the same module are equivalent.  This is the comparison
  lemma that makes filtration-independent invariants well defined.
* `isCompatible_induced`: an `A`-submodule inherits a compatible filtration.
* `isGood_of_subfiltrationNoetherian` and `isGood_induced`: the induced
  filtration is good, given an explicitly named ascending-chain hypothesis on
  compatible subfiltrations and an explicitly named degreewise
  finite-generation hypothesis.  The chain hypothesis is the Noetherian input
  that this file does not prove; see its docstring.

Nothing here assumes that `A` is commutative, Noetherian, or an algebra of
differential operators.
-/

namespace AlgebraicAnalysis.GoodFiltration

open Submodule

universe u v w

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [Semiring A] [Algebra R A]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/-! ## Elementary consequences of the ring-filtration conditions -/

/-- With `1 ∈ F 0` and `F` ascending, every filtration step contains the
identity, so every `R`-submodule of `M` is contained in `F k • P`. -/
theorem le_smul_self {F : ℕ → Submodule R A} (hFmono : Monotone F)
    (hFone : (1 : A) ∈ F 0) (k : ℕ) (P : Submodule R M) : P ≤ F k • P := by
  intro x hx
  have h1 : (1 : A) ∈ F k := hFmono (Nat.zero_le k) hFone
  simpa using Submodule.smul_mem_smul h1 hx

/-- Associativity of the submodule action, in the form used throughout. -/
theorem mul_smul_eq (I J : Submodule R A) (P : Submodule R M) :
    (I * J) • P = I • (J • P) :=
  Submodule.smul_assoc I J P

/-- With `1 ∈ F 0` and `F i * F 0 ≤ F i`, multiplying by the zeroth step is
the identity on filtration steps. -/
theorem mul_zeroth_step_eq {F : ℕ → Submodule R A} (hFone : (1 : A) ∈ F 0)
    (hFmul : ∀ i j, F i * F j ≤ F (i + j)) (i : ℕ) : F i * F 0 = F i := by
  refine le_antisymm ?_ fun a ha => ?_
  · simpa using hFmul i 0
  · simpa using Submodule.mul_mem_mul ha hFone

/-! ## Compatible and good filtrations -/

/-- A filtration of the `A`-module `M` compatible with the family `F` of
`R`-submodules of `A`: ascending, stable under the `F`-action with the
expected index shift, and exhaustive.  Nothing is assumed about `F` itself
here. -/
structure IsCompatible (F : ℕ → Submodule R A) (G : ℕ → Submodule R M) : Prop where
  /-- The filtration is ascending. -/
  mono : Monotone G
  /-- The `i`-th step of `F` moves the `j`-th step of `G` into step `i + j`. -/
  smul_le : ∀ i j, F i • G j ≤ G (i + j)
  /-- The filtration exhausts `M`. -/
  exhaustive : ⨆ i, G i = ⊤

/-- Every element of `M` lies in some step of a compatible filtration. -/
theorem IsCompatible.exists_mem {F : ℕ → Submodule R A} {G : ℕ → Submodule R M}
    (hG : IsCompatible F G) (x : M) : ∃ n, x ∈ G n := by
  have hmem : x ∈ ⨆ i, G i := by rw [hG.exhaustive]; trivial
  exact (Submodule.mem_iSup_of_directed G hG.mono.directed_le).1 hmem

/-- A *good* filtration: some step `d` is generated over `F 0` by a finite
set, and past `d` the filtration is produced from that step by the action of
`F`.  Nothing is asserted about the steps below `d`. -/
def IsGood (F : ℕ → Submodule R A) (G : ℕ → Submodule R M) : Prop :=
  ∃ d : ℕ, ∃ s : Finset M,
    G d = F 0 • Submodule.span R (s : Set M) ∧ ∀ i : ℕ, G (d + i) = F i • G d

/-- If the ring filtration is multiplicatively generated, that is
`F (i + j) ≤ F i * F j` in addition to the defining condition
`F i * F j ≤ F (i + j)`, then a good filtration satisfies the stronger
stabilisation statement `G (i + j) = F i • G j` for every `j` past the
stabilisation index. -/
theorem IsGood.exists_smul_eq {F : ℕ → Submodule R A} {G : ℕ → Submodule R M}
    (hFmul : ∀ i j, F i * F j ≤ F (i + j)) (hFgen : ∀ i j, F (i + j) ≤ F i * F j)
    (hgood : IsGood F G) : ∃ d : ℕ, ∀ i j, d ≤ j → G (i + j) = F i • G j := by
  obtain ⟨d, s, -, hstab⟩ := hgood
  refine ⟨d, fun i j hj => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hij : i + (d + k) = d + (i + k) := by ring
  rw [hij, hstab (i + k), hstab k, ← mul_smul_eq]
  exact congrArg (fun I : Submodule R A => I • G d) (le_antisymm (hFgen i k) (hFmul i k))

/-! ## The filtration generated by a finite generating set -/

/-- The filtration attached to an `R`-submodule `N` of `M`: the `n`-th step is
`F n • N`. -/
def generated (F : ℕ → Submodule R A) (N : Submodule R M) : ℕ → Submodule R M :=
  fun n => F n • N

/-- If the `A`-span of `N` is everything, then the whole of `A` applied to `N`
is everything. -/
theorem top_smul_eq_top {N : Submodule R M} (hN : Submodule.span A (N : Set M) = ⊤) :
    (⊤ : Submodule R A) • N = ⊤ := by
  have hstable : ∀ (a : A) {x : M}, x ∈ (⊤ : Submodule R A) • N →
      a • x ∈ (⊤ : Submodule R A) • N := by
    intro a x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro b _ y hy
      rw [smul_smul]
      exact Submodule.smul_mem_smul Submodule.mem_top hy
    · intro y z hy hz
      rw [smul_add]
      exact Submodule.add_mem _ hy hz
  refine top_le_iff.1 fun x hxtop => ?_
  clear hxtop
  have hx : x ∈ Submodule.span A (N : Set M) := by rw [hN]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
      simpa using
        Submodule.smul_mem_smul (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule R A)) hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul a y _ hy => exact hstable a hy

/-- The generated filtration is compatible, provided the ring filtration is
ascending, multiplicative for the index shift, exhaustive, and `N` generates
`M` as an `A`-module. -/
theorem isCompatible_generated {F : ℕ → Submodule R A} {N : Submodule R M}
    (hFmono : Monotone F) (hFmul : ∀ i j, F i * F j ≤ F (i + j))
    (hFtop : ⨆ i, F i = ⊤) (hN : Submodule.span A (N : Set M) = ⊤) :
    IsCompatible F (generated F N) where
  mono := fun i j h => Submodule.smul_mono_left (hFmono h)
  smul_le := fun i j => by
    show F i • (F j • N) ≤ F (i + j) • N
    refine le_trans (le_of_eq (mul_smul_eq (F i) (F j) N).symm) ?_
    exact Submodule.smul_mono_left (hFmul i j)
  exhaustive := by
    have : ⨆ n, generated F N n = (⨆ n, F n) • N := Submodule.iSup_smul.symm
    rw [this, hFtop, top_smul_eq_top hN]

/-- The generated filtration is good: it stabilises at index `0`. -/
theorem isGood_generated {F : ℕ → Submodule R A} (hFone : (1 : A) ∈ F 0)
    (hFmul : ∀ i j, F i * F j ≤ F (i + j)) (s : Finset M) :
    IsGood F (generated F (Submodule.span R (s : Set M))) := by
  refine ⟨0, s, rfl, fun i => ?_⟩
  show F (0 + i) • Submodule.span R (s : Set M)
      = F i • (F 0 • Submodule.span R (s : Set M))
  rw [Nat.zero_add, ← mul_smul_eq, mul_zeroth_step_eq hFone hFmul]

/-- Every finitely generated module over a filtered ring carries a good
filtration, namely the one generated by a finite generating set. -/
theorem exists_isGood_of_finite {F : ℕ → Submodule R A} (hFmono : Monotone F)
    (hFone : (1 : A) ∈ F 0) (hFmul : ∀ i j, F i * F j ≤ F (i + j))
    (hFtop : ⨆ i, F i = ⊤) [Module.Finite A M] :
    ∃ G : ℕ → Submodule R M, IsCompatible F G ∧ IsGood F G := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  have hspan : Submodule.span A ((Submodule.span R (s : Set M) : Submodule R M) : Set M) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← hs]
    exact Submodule.span_le.2 fun x hx =>
      Submodule.subset_span (Submodule.subset_span hx)
  exact ⟨generated F (Submodule.span R (s : Set M)),
    isCompatible_generated hFmono hFmul hFtop hspan, isGood_generated hFone hFmul s⟩

/-! ## Comparison of good filtrations -/

/-- A good filtration is contained in a fixed shift of any compatible
filtration of the same module.  Only ascendingness of `G` is used, together
with compatibility of `G'`; nothing is assumed about the ring filtration. -/
theorem exists_shift_le {F : ℕ → Submodule R A} {G G' : ℕ → Submodule R M}
    (hGmono : Monotone G) (hG' : IsCompatible F G') (hgood : IsGood F G) :
    ∃ c : ℕ, ∀ n, G n ≤ G' (n + c) := by
  obtain ⟨d, s, hgen, hstab⟩ := hgood
  choose g hg using fun x : M => hG'.exists_mem x
  refine ⟨s.sup g, fun n => ?_⟩
  set c := s.sup g
  have hspan : Submodule.span R (s : Set M) ≤ G' c := by
    refine Submodule.span_le.2 fun x hx => ?_
    exact hG'.mono (Finset.le_sup (f := g) hx) (hg x)
  have hd : G d ≤ G' c := by
    rw [hgen]
    refine le_trans (Submodule.smul_mono le_rfl hspan) ?_
    simpa using hG'.smul_le 0 c
  intro x hx
  rcases le_or_gt n d with hn | hn
  · exact hG'.mono (by omega) (hd (hGmono hn hx))
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn.le
    have hmem : x ∈ F i • G d := by rw [← hstab i]; exact hx
    have : F i • G d ≤ G' (i + c) := le_trans (Submodule.smul_mono le_rfl hd) (hG'.smul_le i c)
    exact hG'.mono (by omega) (this hmem)

/-- Any two good filtrations on the same module are equivalent: each is
squeezed between the shifts of the other by one fixed constant.  This is the
comparison statement that makes invariants computed from a good filtration
independent of the choice of good filtration. -/
theorem exists_shift_le_and_le {F : ℕ → Submodule R A} {G G' : ℕ → Submodule R M}
    (hG : IsCompatible F G) (hG' : IsCompatible F G')
    (hgood : IsGood F G) (hgood' : IsGood F G') :
    ∃ c : ℕ, ∀ n, G n ≤ G' (n + c) ∧ G' n ≤ G (n + c) := by
  obtain ⟨c₁, h₁⟩ := exists_shift_le hG.mono hG' hgood
  obtain ⟨c₂, h₂⟩ := exists_shift_le hG'.mono hG hgood'
  refine ⟨max c₁ c₂, fun n => ⟨?_, ?_⟩⟩
  · exact (h₁ n).trans (hG'.mono (by omega))
  · exact (h₂ n).trans (hG.mono (by omega))

/-! ## The induced filtration on a submodule -/

/-- The filtration induced on an `A`-submodule `N` of `M`: the `n`-th step
consists of the elements of `N` lying in `G n`. -/
def induced (G : ℕ → Submodule R M) (N : Submodule A M) (n : ℕ) : Submodule R N where
  carrier := {x : N | (x : M) ∈ G n}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simpa using (G n).add_mem hx hy
  smul_mem' := by
    intro r x hx
    simpa using (G n).smul_mem r hx

@[simp]
theorem mem_induced {G : ℕ → Submodule R M} {N : Submodule A M} {n : ℕ} {x : N} :
    x ∈ induced G N n ↔ (x : M) ∈ G n := Iff.rfl

/-- A submodule of a module with a compatible filtration inherits a
compatible filtration. -/
theorem isCompatible_induced {F : ℕ → Submodule R A} {G : ℕ → Submodule R M}
    (hG : IsCompatible F G) (N : Submodule A M) :
    IsCompatible F (induced G N) where
  mono := fun i j h x hx => hG.mono h hx
  smul_le := by
    intro i j
    refine Submodule.smul_le.2 fun a ha x hx => ?_
    have : (a : A) • (x : M) ∈ G (i + j) :=
      hG.smul_le i j (Submodule.smul_mem_smul ha hx)
    simpa using this
  exhaustive := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨n, hn⟩ := hG.exists_mem (x : M)
    exact Submodule.mem_iSup_of_mem n hn

/-- **Named hypothesis.** `SubfiltrationNoetherian F G` is the ascending-chain
condition on compatible subfiltrations of `G`: every ascending chain
`K 0 ≤ K 1 ≤ ⋯` of ascending, `F`-stable families of `R`-submodules bounded
by `G` is eventually constant.

Under the dictionary between such families and graded submodules of the Rees
module `⨁ₙ G n` over the Rees ring `⨁ₙ F n`, this says exactly that the Rees
module of `G` is a Noetherian module; equivalently, for a good `G`, that the
associated graded module is Noetherian over the associated graded ring.  The
pinned Mathlib contains neither the Rees ring of a filtered ring nor the
associated graded ring, so this condition is carried here as an explicit
hypothesis rather than derived from Noetherianity of the associated graded
ring. -/
def SubfiltrationNoetherian (F : ℕ → Submodule R A) (G : ℕ → Submodule R M) : Prop :=
  ∀ K : ℕ → ℕ → Submodule R M,
    (∀ d, Monotone (K d)) →
    (∀ d i j, F i • K d j ≤ K d (i + j)) →
    (∀ d n, K d n ≤ G n) →
    (∀ d e, d ≤ e → ∀ n, K d n ≤ K e n) →
    ∃ c : ℕ, ∀ d, c ≤ d → ∀ n, K d n = K c n

/-- A compatible filtration is good as soon as

* the ring filtration is ascending, contains `1` in step `0`, satisfies the
  defining condition `F i * F j ≤ F (i + j)` and is multiplicatively generated
  in the sense `F (i + j) ≤ F i * F j`;
* every step of `G` is generated over `F 0` by a finite set (`hfg`);
* the ascending-chain hypothesis `SubfiltrationNoetherian F G` holds.

The proof is the standard truncation argument: the truncations
`n ↦ if n ≤ d then G n else F (n - d) • G d` form an ascending chain of
compatible subfiltrations of `G`, and the index at which that chain becomes
constant is a stabilisation index for `G`.

Only the stabilisation clause of `IsGood` is derived here; the finite
generation clause is supplied by `hfg`. -/
theorem isGood_of_subfiltrationNoetherian {F : ℕ → Submodule R A} {G : ℕ → Submodule R M}
    (hFmono : Monotone F) (hFone : (1 : A) ∈ F 0)
    (hFmul : ∀ i j, F i * F j ≤ F (i + j)) (hFgen : ∀ i j, F (i + j) ≤ F i * F j)
    (hGmono : Monotone G) (hGsmul : ∀ i j, F i • G j ≤ G (i + j))
    (hfg : ∀ n, ∃ s : Finset M, G n = F 0 • Submodule.span R (s : Set M))
    (hacc : SubfiltrationNoetherian F G) : IsGood F G := by
  set T : ℕ → ℕ → Submodule R M :=
    fun d n => if n ≤ d then G n else F (n - d) • G d with hT
  have hTle : ∀ d n, T d n ≤ G n := by
    intro d n
    by_cases h : n ≤ d
    · simp [hT, h]
    · have hn : n - d + d = n := by omega
      simp only [hT, if_neg h]
      exact le_trans (hGsmul (n - d) d) (le_of_eq (congrArg G hn))
  have hTmono : ∀ d, Monotone (T d) := by
    intro d n m h
    by_cases hn : n ≤ d
    · by_cases hm : m ≤ d
      · simp only [hT, if_pos hn, if_pos hm]
        exact hGmono h
      · simp only [hT, if_pos hn, if_neg hm]
        exact le_trans (hGmono hn) (le_smul_self hFmono hFone _ _)
    · have hm : ¬ m ≤ d := by omega
      simp only [hT, if_neg hn, if_neg hm]
      exact Submodule.smul_mono_left (hFmono (by omega))
  have hTsmul : ∀ d i j, F i • T d j ≤ T d (i + j) := by
    intro d i j
    by_cases hj : j ≤ d
    · simp only [hT, if_pos hj]
      by_cases hij : i + j ≤ d
      · simp only [if_pos hij]
        exact hGsmul i j
      · simp only [if_neg hij]
        have hi : (i + j - d) + (d - j) = i := by omega
        have hdj : d - j + j = d := by omega
        have hle : F i ≤ F (i + j - d) * F (d - j) := by
          have h := hFgen (i + j - d) (d - j)
          rwa [hi] at h
        calc F i • G j ≤ (F (i + j - d) * F (d - j)) • G j :=
              Submodule.smul_mono_left hle
          _ = F (i + j - d) • (F (d - j) • G j) := mul_smul_eq _ _ _
          _ ≤ F (i + j - d) • G d := by
              refine Submodule.smul_mono le_rfl ?_
              exact le_trans (hGsmul (d - j) j) (le_of_eq (congrArg G hdj))
    · have hij : ¬ i + j ≤ d := by omega
      simp only [hT, if_neg hj, if_neg hij]
      calc F i • (F (j - d) • G d) = (F i * F (j - d)) • G d := (mul_smul_eq _ _ _).symm
        _ ≤ F (i + (j - d)) • G d := Submodule.smul_mono_left (hFmul _ _)
        _ = F (i + j - d) • G d := by
            exact congrArg (fun k => F k • G d) (by omega)
  have hTchain : ∀ d e, d ≤ e → ∀ n, T d n ≤ T e n := by
    intro d e hde n
    by_cases hn : n ≤ d
    · have hne : n ≤ e := by omega
      simp only [hT, if_pos hn, if_pos hne]
      exact le_rfl
    · by_cases hne : n ≤ e
      · simp only [hT, if_neg hn, if_pos hne]
        have := hTle d n
        simpa [hT, if_neg hn] using this
      · simp only [hT, if_neg hn, if_neg hne]
        have hsplit : (n - e) + (e - d) = n - d := by omega
        have hed : e - d + d = e := by omega
        have hle : F (n - d) ≤ F (n - e) * F (e - d) := by
          have h := hFgen (n - e) (e - d)
          rwa [hsplit] at h
        calc F (n - d) • G d ≤ (F (n - e) * F (e - d)) • G d :=
              Submodule.smul_mono_left hle
          _ = F (n - e) • (F (e - d) • G d) := mul_smul_eq _ _ _
          _ ≤ F (n - e) • G e := by
              refine Submodule.smul_mono le_rfl ?_
              exact le_trans (hGsmul (e - d) d) (le_of_eq (congrArg G hed))
  obtain ⟨c, hc⟩ := hacc T hTmono hTsmul hTle hTchain
  obtain ⟨s, hs⟩ := hfg c
  refine ⟨c, s, hs, fun i => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine le_antisymm ?_ ?_
    · simpa using le_smul_self hFmono hFone 0 (G (c + 0))
    · simpa using hGsmul 0 c
  · have h1 : T (c + i) (c + i) = G (c + i) := by simp [hT]
    have h2 : T c (c + i) = F i • G c := by
      have hne : ¬ c + i ≤ c := by omega
      simp only [hT, if_neg hne]
      exact congrArg (fun k => F k • G c) (by omega)
    rw [← h1, hc (c + i) (by omega) (c + i), h2]

/-- A submodule of a module with a compatible filtration (in particular with a
good one) carries the induced filtration, and that induced filtration is
again good, given the two explicitly named inputs: degreewise finite
generation of the induced filtration over `F 0`, and the ascending-chain
hypothesis
`SubfiltrationNoetherian` for the induced filtration.  The latter is what a
Noetherian associated graded ring supplies; see its docstring for the exact
statement and for why it is not derived here. -/
theorem isGood_induced {F : ℕ → Submodule R A} {G : ℕ → Submodule R M}
    (hFmono : Monotone F) (hFone : (1 : A) ∈ F 0)
    (hFmul : ∀ i j, F i * F j ≤ F (i + j)) (hFgen : ∀ i j, F (i + j) ≤ F i * F j)
    (hG : IsCompatible F G) (N : Submodule A M)
    (hfg : ∀ n, ∃ t : Finset N, induced G N n = F 0 • Submodule.span R (t : Set N))
    (hacc : SubfiltrationNoetherian F (induced G N)) :
    IsGood F (induced G N) := by
  have hind := isCompatible_induced hG N
  exact isGood_of_subfiltrationNoetherian hFmono hFone hFmul hFgen hind.mono hind.smul_le hfg hacc

/-- The induced filtration on a submodule is squeezed inside a fixed shift of
any compatible filtration of that submodule, once it is known to be good. -/
theorem exists_shift_le_induced {F : ℕ → Submodule R A} {G : ℕ → Submodule R M}
    {N : Submodule A M} {H : ℕ → Submodule R N}
    (hG : IsCompatible F G) (hH : IsCompatible F H)
    (hgood : IsGood F (induced G N)) :
    ∃ c : ℕ, ∀ n, induced G N n ≤ H (n + c) :=
  exists_shift_le (isCompatible_induced hG N).mono hH hgood

end AlgebraicAnalysis.GoodFiltration
