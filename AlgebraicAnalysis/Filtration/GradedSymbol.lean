module
public import AlgebraicAnalysis.Filtration.RingFiltration
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Data.Finset.NatAntidiagonal

@[expose] public section

/-!
# Principal symbols with values in a commutative graded algebra

For a ring filtration `φ : RingFiltration R A` of a (possibly noncommutative)
`R`-algebra `A`, a `RingFiltration.GradedSymbol φ 𝒜` identifies the
associated graded ring `gr A = ⨁ F n / F (n-1)` with a commutative
`ℕ`-graded `R`-algebra `G = ⨁ 𝒜 n`. It consists of `R`-linear maps
`gr n : F n → 𝒜 n` which are surjective, have kernel `F (n-1)` (with
`F (-1) = 0`), and are multiplicative. These conditions say precisely that
each `gr n` induces `F n / F (n-1) ≃ 𝒜 n`
(`RingFiltration.GradedSymbol.gradedQuotientEquiv`) and that these
isomorphisms carry the graded multiplication of `gr A` to that of `G`.
Hypotheses such as "`gr A` is a commutative Noetherian ring" are stated
through such an identification, as in [McConnell–Robson, *Noncommutative
Noetherian Rings*, 1.6.9 and 6.5.6]; the ring structure of `gr A` itself is
never constructed.

The interface adapts the `FilteredAlgebraData` symbol interface of
`itpplasma/generalized-stafford-formal` (archived `GeneralizedStafford/Setting.lean`)
to the shared `RingFiltration` structure.

## Main definitions

* `RingFiltration.GradedSymbol φ 𝒜`: the symbol data.
* `RingFiltration.GradedSymbol.grAt n u`: the degree-`n` symbol of `u`,
  extended by zero outside `F n`.
* `RingFiltration.ofGradedAlgebra 𝒜` and `RingFiltration.GradedSymbol.ofGradedAlgebra 𝒜`:
  a graded ring filtered by degree, with associated graded ring itself.
-/

namespace AlgebraicAnalysis

open DirectSum

namespace RingFiltration

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing G] [Algebra R G]

/-- Principal-symbol data identifying the associated graded ring of `φ` with
the commutative graded algebra `G = ⨁ 𝒜 n`: surjective `R`-linear maps
`gr n : F n → 𝒜 n` with kernel `F (n - 1)` that multiply symbols. -/
structure GradedSymbol (φ : RingFiltration R A) (𝒜 : ℕ → Submodule R G) where
  /-- The degree-`n` symbol map `F n → F n / F (n-1) ≃ 𝒜 n`. -/
  gr : ∀ n, φ.F n →ₗ[R] 𝒜 n
  /-- Every homogeneous element of `G` is a symbol. -/
  gr_surjective : ∀ n, Function.Surjective (gr n)
  /-- The kernel of `gr n` is the previous filtration piece. -/
  gr_eq_zero_iff : ∀ n (x : φ.F n), gr n x = 0 ↔ (x : A) ∈ φ.below n
  /-- Symbols multiply: `gr (i+j) (x y) = gr i x * gr j y`. -/
  gr_mul : ∀ i j (x : φ.F i) (y : φ.F j),
    ((gr (i + j) ⟨x * y, φ.mul_mem_add x.2 y.2⟩ : 𝒜 (i + j)) : G) =
      (gr i x : G) * (gr j y : G)

namespace GradedSymbol

variable {φ : RingFiltration R A} {𝒜 : ℕ → Submodule R G} (S : GradedSymbol φ 𝒜)

/-- The symbol map induces `F n / F (n-1) ≃ 𝒜 n`. -/
noncomputable def gradedQuotientEquiv (n : ℕ) : φ.GradedQuotient n ≃ₗ[R] 𝒜 n :=
  (Submodule.quotEquivOfEq (φ.belowInF n) (LinearMap.ker (S.gr n)) (by
    ext x
    rw [LinearMap.mem_ker, S.gr_eq_zero_iff]
    rfl)).trans ((S.gr n).quotKerEquivOfSurjective (S.gr_surjective n))

theorem gradedQuotientEquiv_mk (n : ℕ) (x : φ.F n) :
    S.gradedQuotientEquiv n (Submodule.Quotient.mk x) = S.gr n x :=
  rfl

/-- The degree-`n` symbol of `u`, extended by zero outside `F n`. -/
noncomputable def grAt (n : ℕ) (u : A) : G := by
  classical exact if h : u ∈ φ.F n then ((S.gr n ⟨u, h⟩ : 𝒜 n) : G) else 0

theorem grAt_of_mem {n : ℕ} {u : A} (h : u ∈ φ.F n) :
    S.grAt n u = ((S.gr n ⟨u, h⟩ : 𝒜 n) : G) := by
  simp [grAt, h]

theorem grAt_mem (n : ℕ) (u : A) : S.grAt n u ∈ 𝒜 n := by
  unfold grAt
  split_ifs
  · exact (S.gr n _).2
  · exact Submodule.zero_mem _

theorem grAt_sub {n : ℕ} {u v : A} (hu : u ∈ φ.F n) (hv : v ∈ φ.F n) :
    S.grAt n (u - v) = S.grAt n u - S.grAt n v := by
  rw [S.grAt_of_mem hu, S.grAt_of_mem hv, S.grAt_of_mem (Submodule.sub_mem _ hu hv)]
  have : (⟨u - v, Submodule.sub_mem _ hu hv⟩ : φ.F n) = ⟨u, hu⟩ - ⟨v, hv⟩ := rfl
  rw [this, map_sub]
  rfl

theorem grAt_eq_zero_iff {n : ℕ} {u : A} (hu : u ∈ φ.F n) :
    S.grAt n u = 0 ↔ u ∈ φ.below n := by
  rw [S.grAt_of_mem hu, Submodule.coe_eq_zero, S.gr_eq_zero_iff]

/-- Two elements of `F n` have the same degree-`n` symbol iff their
difference lies in `F (n - 1)`. -/
theorem grAt_eq_grAt_iff {n : ℕ} {u v : A} (hu : u ∈ φ.F n) (hv : v ∈ φ.F n) :
    S.grAt n u = S.grAt n v ↔ u - v ∈ φ.below n := by
  rw [← S.grAt_eq_zero_iff (Submodule.sub_mem _ hu hv), S.grAt_sub hu hv, sub_eq_zero]

theorem grAt_mul {i j : ℕ} {u v : A} (hu : u ∈ φ.F i) (hv : v ∈ φ.F j) :
    S.grAt (i + j) (u * v) = S.grAt i u * S.grAt j v := by
  rw [S.grAt_of_mem hu, S.grAt_of_mem hv, S.grAt_of_mem (φ.mul_mem_add hu hv)]
  exact S.gr_mul i j ⟨u, hu⟩ ⟨v, hv⟩

theorem grAt_mul' {i j n : ℕ} (h : i + j = n) {u v : A} (hu : u ∈ φ.F i)
    (hv : v ∈ φ.F j) : S.grAt n (u * v) = S.grAt i u * S.grAt j v := by
  subst h
  exact S.grAt_mul hu hv

theorem exists_grAt_eq {n : ℕ} {g : G} (hg : g ∈ 𝒜 n) :
    ∃ u ∈ φ.F n, S.grAt n u = g := by
  obtain ⟨x, hx⟩ := S.gr_surjective n ⟨g, hg⟩
  exact ⟨x, x.2, by rw [S.grAt_of_mem x.2]; simp [hx]⟩

end GradedSymbol

/-! ## A graded ring filtered by degree -/

section OfGradedAlgebra

variable (𝒜 : ℕ → Submodule R G) [GradedAlgebra 𝒜]

/-- The degree filtration of a graded algebra: `F n` consists of the elements
whose homogeneous components above degree `n` vanish. -/
def degreeLE (n : ℕ) : Submodule R G where
  carrier := {g | ∀ i, n < i → decompose 𝒜 g i = 0}
  add_mem' := by
    intro a b ha hb i hi
    rw [decompose_add, add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' := by
    intro i _
    rw [decompose_zero, zero_apply]
  smul_mem' := by
    intro c a ha i hi
    rw [decompose_smul, smul_apply, ha i hi, smul_zero]

variable {𝒜}

theorem mem_degreeLE {n : ℕ} {g : G} :
    g ∈ degreeLE 𝒜 n ↔ ∀ i, n < i → decompose 𝒜 g i = 0 := Iff.rfl

theorem mem_degreeLE_of_mem {n : ℕ} {g : G} (hg : g ∈ 𝒜 n) : g ∈ degreeLE 𝒜 n :=
  fun _ hi => Subtype.ext (decompose_of_mem_ne 𝒜 hg hi.ne)

/-- The product formula for homogeneous components of a product. -/
theorem coe_decompose_mul_eq_sum (x y : G) (k : ℕ) :
    (decompose 𝒜 (x * y) k : G) =
      ∑ ij ∈ Finset.antidiagonal k, (decompose 𝒜 x ij.1 : G) * decompose 𝒜 y ij.2 := by
  rw [decompose_mul, coe_mul_apply_eq_sum_antidiagonal]

/-- The degree filtration is submultiplicative. -/
theorem degreeLE_mul_le (i j : ℕ) :
    degreeLE 𝒜 i * degreeLE 𝒜 j ≤ degreeLE 𝒜 (i + j) := by
  rw [Submodule.mul_le]
  intro x hx y hy k hk
  apply Subtype.ext
  rw [coe_decompose_mul_eq_sum, ZeroMemClass.coe_zero]
  refine Finset.sum_eq_zero fun ab hab => ?_
  rw [Finset.mem_antidiagonal] at hab
  rcases lt_or_ge i ab.1 with h | h
  · rw [hx _ h, ZeroMemClass.coe_zero, zero_mul]
  · rw [hy _ (by omega), ZeroMemClass.coe_zero, mul_zero]

variable (𝒜) in
/-- The degree filtration of a graded algebra. -/
def ofGradedAlgebra : RingFiltration R G where
  F := degreeLE 𝒜
  mono := fun _ _ hab _ hx i hi => hx i (lt_of_le_of_lt hab hi)
  one_mem := mem_degreeLE_of_mem SetLike.GradedOne.one_mem
  mul_le := degreeLE_mul_le
  exhaustive := by
    classical
    refine eq_top_iff.mpr fun g _ => ?_
    let n := (decompose 𝒜 g).support.sup id
    refine Submodule.mem_iSup_of_mem n fun i hi => ?_
    by_contra hne
    have : i ∈ (decompose 𝒜 g).support := DFinsupp.mem_support_iff.mpr hne
    exact absurd (Finset.le_sup (f := id) this) (not_le.mpr hi)

@[simp] theorem ofGradedAlgebra_F (n : ℕ) : (ofGradedAlgebra 𝒜).F n = degreeLE 𝒜 n := rfl

variable (𝒜) in
/-- The symbol of the degree filtration of a graded algebra is the top
homogeneous component; its associated graded ring is the algebra itself. -/
def GradedSymbol.ofGradedAlgebra : GradedSymbol (ofGradedAlgebra 𝒜) 𝒜 where
  gr n :=
    { toFun := fun x => decompose 𝒜 (x : G) n
      map_add' := fun x y => by
        change decompose 𝒜 ((x : G) + y) n = _
        rw [decompose_add]
        rfl
      map_smul' := fun c x => by
        change decompose 𝒜 (c • (x : G)) n = _
        rw [decompose_smul]
        rfl }
  gr_surjective n := fun g =>
    ⟨⟨g, mem_degreeLE_of_mem g.2⟩, Subtype.ext (decompose_of_mem_same 𝒜 g.2)⟩
  gr_eq_zero_iff n x := by
    obtain ⟨x, hx⟩ := x
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    cases n with
    | zero =>
      rw [below_zero, Submodule.mem_bot]
      constructor
      · intro h0
        apply (decompose 𝒜).injective
        ext i : 1
        rw [decompose_zero, zero_apply]
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact h0
        · exact hx i hi
      · rintro rfl
        rw [decompose_zero, zero_apply]
    | succ n =>
      rw [below_succ]
      constructor
      · intro h0 i hi
        rcases Nat.lt_or_ge (n + 1) i with h | h
        · exact hx i h
        · obtain rfl : i = n + 1 := by omega
          exact h0
      · intro h
        exact h (n + 1) (Nat.lt_succ_self n)
  gr_mul i j x y := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [coe_decompose_mul_eq_sum, Finset.sum_eq_single (i, j)]
    · rintro ⟨a, b⟩ hab hne
      rw [Finset.mem_antidiagonal] at hab
      rcases lt_or_ge i a with h | h
      · rw [hx _ h, ZeroMemClass.coe_zero, zero_mul]
      · have hb : j < b := by
          by_contra hb
          exact hne (Prod.ext (by dsimp only; omega) (by dsimp only; omega))
        rw [hy _ hb, ZeroMemClass.coe_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_antidiagonal.mpr (rfl : i + j = i + j)) h

end OfGradedAlgebra

end RingFiltration

end AlgebraicAnalysis
