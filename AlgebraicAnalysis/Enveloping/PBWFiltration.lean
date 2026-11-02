module
public import AlgebraicAnalysis.Filtration.RingFiltration
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-!
# PBW filtration of a quotient of a universal enveloping algebra

Let `L` be a Lie algebra over a field `k`, and let `π : U(L) →ₐ[k] R` be a
surjective algebra map onto a `k`-algebra `R` (this covers `U(L)` itself and
every quotient `U(L) / J`). Let `gen x = π (ι x)` be the image of `x ∈ L`.

The **PBW filtration** of `R` is `Fₙ = span {x₁ ⋯ xⱼ : j ≤ n, xᵢ ∈ L}`, the span of
products of at most `n` Lie elements. It is an ascending filtration in the sense
of `RingFiltration`.

The only commutation fact used is the Lie bracket identity
`gen x * gen y - gen y * gen x = gen [x, y]`, which lies in `F₁`. Hence a
product of degree-one generators changes, under a permutation of its factors,
only by an element of lower filtration (`wordProd_sub_mem_pbwPiece`). No
Poincaré–Birkhoff–Witt theorem is used: only this spanning direction is needed.

## Main definitions and results

* `gen π x`, `wordProd π w`: the image of `x ∈ L` and the ordered product of a word.
* `pbwPiece π n`: the span of products of at most `n` Lie elements, that is `Fₙ`.
* `pbwFiltration π hπ`: the PBW filtration of `R` as a `RingFiltration k R`.
* `wordProd_sub_mem_pbwPiece`: permuting a word changes its product only in lower
  filtration.

The symbol presentation by the polynomial ring and the Krull dimension
consequences are in `AlgebraicAnalysis.Enveloping.Presentation`.
-/

namespace AlgebraicAnalysis.Enveloping

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section Definitions

variable {k : Type*} [Field k] {L : Type*} [LieRing L] [LieAlgebra k L]
variable {R : Type*} [Ring R] [Algebra k R]

/-- The image in `R` of a Lie element `x`, namely `π (ι x)`. -/
def gen (π : UniversalEnvelopingAlgebra k L →ₐ[k] R) (x : L) : R :=
  π (ι k x)

/-- The product `w₁ w₂ ⋯ wₙ` in `R` of the images of a word `w` of Lie elements, in the
written order. -/
def wordProd (π : UniversalEnvelopingAlgebra k L →ₐ[k] R) (w : List L) : R :=
  (w.map (gen π)).prod

/-- The `n`-th PBW piece `Fₙ`: the `k`-span of products of at most `n` Lie elements. -/
def pbwPiece (π : UniversalEnvelopingAlgebra k L →ₐ[k] R) (n : ℕ) : Submodule k R :=
  Submodule.span k {r | ∃ w : List L, w.length ≤ n ∧ wordProd π w = r}

variable (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)

theorem wordProd_nil : wordProd π ([] : List L) = 1 := by
  simp [wordProd]

theorem wordProd_cons (x : L) (w : List L) :
    wordProd π (x :: w) = gen π x * wordProd π w := by
  simp [wordProd]

theorem wordProd_append (u v : List L) :
    wordProd π (u ++ v) = wordProd π u * wordProd π v := by
  simp [wordProd]

theorem wordProd_singleton (x : L) : wordProd π [x] = gen π x := by
  simp [wordProd]

theorem wordProd_mem_pbwPiece {w : List L} {n : ℕ} (hw : w.length ≤ n) :
    wordProd π w ∈ pbwPiece π n :=
  Submodule.subset_span ⟨w, hw, rfl⟩

theorem pbwPiece_mono {a b : ℕ} (h : a ≤ b) : pbwPiece π a ≤ pbwPiece π b :=
  Submodule.span_mono fun _ ⟨w, hw, hr⟩ => ⟨w, hw.trans h, hr⟩

theorem one_mem_pbwPiece (n : ℕ) : (1 : R) ∈ pbwPiece π n := by
  simpa [wordProd_nil] using wordProd_mem_pbwPiece π (w := []) (n := n) (Nat.zero_le _)

theorem gen_mem_pbwPiece_one (x : L) : gen π x ∈ pbwPiece π 1 := by
  simpa [wordProd_singleton] using wordProd_mem_pbwPiece π (w := [x]) (n := 1) le_rfl

theorem mul_mem_pbwPiece {i j : ℕ} {a b : R} (ha : a ∈ pbwPiece π i)
    (hb : b ∈ pbwPiece π j) : a * b ∈ pbwPiece π (i + j) := by
  have hle : pbwPiece π i * pbwPiece π j ≤ pbwPiece π (i + j) := by
    rw [pbwPiece, pbwPiece, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, ⟨u, hu, rfl⟩, b, ⟨v, hv, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨u ++ v, by simp only [List.length_append]; omega,
      wordProd_append π u v⟩
  exact hle (Submodule.mul_mem_mul ha hb)

/-- The PBW filtration of `R` is submultiplicative. -/
theorem pbwPiece_mul_le (i j : ℕ) : pbwPiece π i * pbwPiece π j ≤ pbwPiece π (i + j) :=
  Submodule.mul_le.mpr fun _ ha _ hb => mul_mem_pbwPiece π ha hb

/-- The PBW pieces exhaust `R` when `π` is surjective: every element of `U(L)` is a sum of
products of Lie generators, by induction on the tensor algebra. -/
theorem iSup_pbwPiece_eq_top (hπ : Function.Surjective π) : ⨆ n, pbwPiece π n = ⊤ := by
  rw [eq_top_iff]
  intro r _
  obtain ⟨u, rfl⟩ := hπ r
  obtain ⟨t, rfl⟩ := Quotient.exists_rep u
  have key : ∀ t : TensorAlgebra k L, ∃ n, π (mkAlgHom k L t) ∈ pbwPiece π n := by
    intro t
    induction t using TensorAlgebra.induction with
    | algebraMap c =>
      refine ⟨0, ?_⟩
      have : π (mkAlgHom k L (algebraMap k (TensorAlgebra k L) c)) = algebraMap k R c := by
        simp
      rw [this, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ c (one_mem_pbwPiece π 0)
    | ι x =>
      refine ⟨1, ?_⟩
      exact gen_mem_pbwPiece_one π x
    | mul a b ha hb =>
      obtain ⟨n, hn⟩ := ha
      obtain ⟨m, hm⟩ := hb
      refine ⟨n + m, ?_⟩
      simp only [map_mul]
      exact mul_mem_pbwPiece π hn hm
    | add a b ha hb =>
      obtain ⟨n, hn⟩ := ha
      obtain ⟨m, hm⟩ := hb
      refine ⟨max n m, ?_⟩
      simp only [map_add]
      exact Submodule.add_mem _ (pbwPiece_mono π (le_max_left n m) hn)
        (pbwPiece_mono π (le_max_right n m) hm)
  obtain ⟨n, hn⟩ := key t
  exact Submodule.mem_iSup_of_mem n hn

end Definitions

section Filtration

variable {k : Type*} [Field k] {L : Type*} [LieRing L] [LieAlgebra k L]
variable {R : Type*} [Ring R] [Algebra k R]

/-- **The PBW filtration.** For a surjective algebra map `π : U(L) → R`, the pieces
`Fₙ = span {products of at most n Lie elements}` form a `RingFiltration k R`. -/
noncomputable def pbwFiltration (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)
    (hπ : Function.Surjective π) : RingFiltration k R where
  F := pbwPiece π
  mono := fun _ _ h => pbwPiece_mono π h
  one_mem := one_mem_pbwPiece π 0
  mul_le := pbwPiece_mul_le π
  exhaustive := iSup_pbwPiece_eq_top π hπ

theorem pbwFiltration_F (π : UniversalEnvelopingAlgebra k L →ₐ[k] R) (hπ : Function.Surjective π)
    (n : ℕ) : (pbwFiltration π hπ).F n = pbwPiece π n :=
  rfl

/-- **Bracket identity.** The commutator of two generators is the generator of their Lie
bracket, `[gen x, gen y] = gen [x, y]`; in particular it lies in `F₁`. -/
theorem gen_bracket (π : UniversalEnvelopingAlgebra k L →ₐ[k] R) (x y : L) :
    gen π x * gen π y - gen π y * gen π x = gen π ⁅x, y⁆ := by
  have h : ι k ⁅x, y⁆ = ι k x * ι k y - ι k y * ι k x := by
    rw [LieHom.map_lie, Ring.lie_def]
  simp only [gen, h, map_sub, map_mul]

/-- Reordering lemma. Permuting the factors of a word changes its product only by an element of
the filtration piece `Fₙ` as soon as the word has length at most `n + 1`. The proof moves one
adjacent transposition at a time; a swap changes the product by `-[gen x, gen y] · (rest)`,
which lies in `F₁ · F_{len rest} ⊆ F_{len rest + 1}`. -/
theorem wordProd_sub_mem_pbwPiece (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)
    {w w' : List L} (h : w.Perm w') :
    ∀ n : ℕ, w.length ≤ n + 1 → wordProd π w - wordProd π w' ∈ pbwPiece π n := by
  induction h with
  | nil =>
    intro n _
    simp [wordProd_nil]
  | @cons x l₁ l₂ hl ih =>
    intro n hn
    cases n with
    | zero =>
      have h1 : l₁ = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hn; omega)
      have h2 : l₂ = [] := List.length_eq_zero_iff.mp (by rw [← hl.length_eq, h1]; rfl)
      subst h1 h2
      simp
    | succ m =>
      simp only [wordProd_cons, ← mul_sub]
      have hm := ih m (by simp only [List.length_cons] at hn; omega)
      exact pbwPiece_mono π (by omega) (mul_mem_pbwPiece π (gen_mem_pbwPiece_one π x) hm)
  | @swap x y l =>
    intro n hn
    simp only [List.length_cons] at hn
    simp only [wordProd_cons]
    have e : gen π y * (gen π x * wordProd π l) - gen π x * (gen π y * wordProd π l) =
        -(gen π ⁅x, y⁆ * wordProd π l) := by
      rw [← gen_bracket π x y]
      noncomm_ring
    rw [e]
    exact Submodule.neg_mem _ (pbwPiece_mono π (by omega)
      (mul_mem_pbwPiece π (gen_mem_pbwPiece_one π ⁅x, y⁆) (wordProd_mem_pbwPiece π le_rfl)))
  | @trans w₁ w₂ w₃ h₁ h₂ ih₁ ih₂ =>
    intro n hn
    have hn' : w₂.length ≤ n + 1 := by rw [← h₁.length_eq]; exact hn
    have := Submodule.add_mem _ (ih₁ n hn) (ih₂ n hn')
    simpa using this

end Filtration

end AlgebraicAnalysis.Enveloping
