module

public import Mathlib.RingTheory.OreLocalization.Ring
public import AlgebraicAnalysis.Module.UniformDimension

@[expose] public section

/-!
# Ore localization of modules: exactness, torsion kernel and uniform dimension

Let `S` be a left Ore set in a ring `A` and `X` a left `A`-module. Mathlib's
`OreLocalization S X`, written `X[S⁻¹]`, consists of fractions `s⁻¹ x` (written
`x /ₒ s`) and is a module over the Ore localization `A[S⁻¹]`. This file adds
the functorial and dimension-theoretic facts used for Goldie rank.

* `OreModule.toLocalization S X : X →ₗ[A] X[S⁻¹]`, `x ↦ x /ₒ 1`, has kernel the
  `S`-torsion elements (`toLocalization_eq_zero_iff`).
* `OreModule.localizationMap S f : X[S⁻¹] →ₗ[A[S⁻¹]] Y[S⁻¹]` is the localization of an
  `A`-linear map `f`. Localization is exact: it preserves injective maps,
  surjective maps and exactness in the middle (`localizationMap_injective`,
  `localizationMap_surjective`, `localizationMap_exact`); in other words `A[S⁻¹]` is flat.
* `OreModule.finite`: the localization of a finitely generated module is
  finitely generated.
* `OreModule.uniformDimGE_iff_of_injective`: if `N` embeds `A`-linearly in an
  `A[S⁻¹]`-module `P` such that every element of `P` is multiplied into `N` by
  an element of `S`, then `N` (over `A`) and `P` (over `A[S⁻¹]`) contain direct
  sums of the same numbers of nonzero submodules. The submodules are compared
  through the `S`-saturation `OreModule.saturation`.

For right modules over a ring `R` and a right Ore set of `R`, apply these facts
with `A = Rᵐᵒᵖ` (see `AlgebraicAnalysis.Goldie.FractionModule`).

## References

J. C. McConnell and J. C. Robson, *Noncommutative Noetherian Rings*, 2.1.16–2.1.17
(flatness and the torsion kernel) and 2.2.13 (uniform dimension is preserved);
K. R. Goodearl and R. B. Warfield, *An Introduction to Noncommutative Noetherian
Rings*, 2nd ed., Chapter 10. Nothing here is new.
-/

namespace AlgebraicAnalysis.OreModule

open OreLocalization

universe u v w

variable {A : Type u} [Ring A] (S : Submonoid A) [OreSet S]

section Functor

variable (X : Type v) [AddCommGroup X] [Module A X]
variable {Y : Type w} [AddCommGroup Y] [Module A Y]
variable {Z : Type*} [AddCommGroup Z] [Module A Z]

/-- The canonical `A`-linear map `X → X[S⁻¹]`, `x ↦ x /ₒ 1`. -/
def toLocalization : X →ₗ[A] OreLocalization S X where
  toFun x := x /ₒ (1 : S)
  map_add' _ _ := add_oreDiv.symm
  map_smul' a x := (smul_oreDiv_one a x).symm

variable {S X}

@[simp]
theorem toLocalization_apply (x : X) : toLocalization S X x = x /ₒ (1 : S) := rfl

/-- Multiplying the fraction `s⁻¹ x` by `s` gives `x`. -/
theorem smul_oreDiv_self (x : X) (s : S) :
    (s : A) • (x /ₒ s) = toLocalization S X x := by
  rw [← oreDiv_one_smul, OreLocalization.smul_cancel]
  rfl

/-- **The torsion kernel.** An element `x` maps to zero in `X[S⁻¹]` if and only
if `s • x = 0` for some `s ∈ S`. -/
theorem toLocalization_eq_zero_iff {x : X} :
    toLocalization S X x = 0 ↔ ∃ s ∈ S, s • x = 0 := by
  rw [toLocalization_apply]
  constructor
  · intro h
    rw [OreLocalization.zero_def, oreDiv_eq_iff] at h
    obtain ⟨u, v, h1, h2⟩ := h
    have huv : (u : A) = v := by simpa using h2
    refine ⟨u, u.2, ?_⟩
    rw [huv, ← h1, smul_zero]
  · rintro ⟨s, hs, hsx⟩
    rw [OreLocalization.expand' x 1 ⟨s, hs⟩, Submonoid.smul_def, hsx, zero_oreDiv]

/-- A fraction `s⁻¹ x` vanishes if and only if `x` maps to zero. -/
theorem oreDiv_eq_zero_iff {x : X} {s : S} :
    x /ₒ s = 0 ↔ toLocalization S X x = 0 := by
  constructor
  · intro h
    rw [← smul_oreDiv_self, h, smul_zero]
  · intro h
    have : x /ₒ s = ((1 : A) /ₒ s) • toLocalization S X x := by
      rw [toLocalization_apply, OreLocalization.one_div_smul, one_mul]
    rw [this, h, smul_zero]

variable (S) in
/-- The localization `X[S⁻¹] → Y[S⁻¹]`, `s⁻¹ x ↦ s⁻¹ f(x)`, of an `A`-linear map
`f : X → Y`. -/
def localizationMap (f : X →ₗ[A] Y) : OreLocalization S X →ₗ[OreLocalization S A] OreLocalization S Y where
  toFun := liftExpand (fun x s => f x /ₒ s) fun x t s ht => by
    rw [map_smul]
    exact OreLocalization.expand (f x) s t ht
  map_add' p q := by
    induction p using OreLocalization.ind with | _ x s =>
    induction q using OreLocalization.ind with | _ y t =>
    rw [oreDiv_add_oreDiv, liftExpand_of, liftExpand_of, liftExpand_of, map_add,
      Submonoid.smul_def, map_smul, map_smul, oreDiv_add_oreDiv, Submonoid.smul_def]
  map_smul' q p := by
    induction q using OreLocalization.ind with | _ r t =>
    induction p using OreLocalization.ind with | _ x s =>
    rw [oreDiv_smul_oreDiv, RingHom.id_apply, liftExpand_of, liftExpand_of, map_smul,
      oreDiv_smul_oreDiv]

@[simp]
theorem localizationMap_oreDiv (f : X →ₗ[A] Y) (x : X) (s : S) : localizationMap S f (x /ₒ s) = f x /ₒ s := rfl

theorem localizationMap_toLocalization (f : X →ₗ[A] Y) (x : X) :
    localizationMap S f (toLocalization S X x) = toLocalization S Y (f x) := rfl

theorem localizationMap_comp_apply (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (p : OreLocalization S X) :
    localizationMap S g (localizationMap S f p) = localizationMap S (g ∘ₗ f) p := by
  induction p using OreLocalization.ind with | _ x s => rfl

/-- Localization preserves injective maps. -/
theorem localizationMap_injective {f : X →ₗ[A] Y} (hf : Function.Injective f) :
    Function.Injective (localizationMap S f) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  induction p using OreLocalization.ind with | _ x s =>
  rw [localizationMap_oreDiv, oreDiv_eq_zero_iff, toLocalization_eq_zero_iff] at hp
  obtain ⟨t, ht, htx⟩ := hp
  rw [oreDiv_eq_zero_iff, toLocalization_eq_zero_iff]
  exact ⟨t, ht, hf (by rw [map_smul, htx, map_zero])⟩

/-- Localization preserves surjective maps. -/
theorem localizationMap_surjective {f : X →ₗ[A] Y} (hf : Function.Surjective f) :
    Function.Surjective (localizationMap S f) := by
  intro q
  induction q using OreLocalization.ind with | _ y s =>
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨x /ₒ s, rfl⟩

/-- **Ore localization is exact** (`A[S⁻¹]` is a flat right `A`-module): the
localization of an exact sequence `X → Y → Z` is exact. -/
theorem localizationMap_exact {f : X →ₗ[A] Y} {g : Y →ₗ[A] Z} (hfg : Function.Exact f g) :
    Function.Exact (localizationMap S f) (localizationMap S g) := by
  intro q
  induction q using OreLocalization.ind with | _ y s =>
  rw [localizationMap_oreDiv, oreDiv_eq_zero_iff, toLocalization_eq_zero_iff]
  constructor
  · rintro ⟨t, ht, hty⟩
    obtain ⟨x, hx⟩ := (hfg (t • y)).mp (by rw [map_smul, hty])
    refine ⟨x /ₒ (⟨t, ht⟩ * s), ?_⟩
    rw [localizationMap_oreDiv, hx, OreLocalization.expand' y s ⟨t, ht⟩, Submonoid.smul_def]
  · rintro ⟨p, hp⟩
    induction p using OreLocalization.ind with | _ x u =>
    rw [localizationMap_oreDiv, oreDiv_eq_iff] at hp
    obtain ⟨a, b, h1, h2⟩ := hp
    refine ⟨a, a.2, ?_⟩
    rw [← map_smul, ← Submonoid.smul_def, h1, map_smul, hfg.apply_apply_eq_zero, smul_zero]

variable (S X) in
/-- The localization of a finitely generated module is finitely generated over
the localized ring. -/
theorem finite [Module.Finite A X] : Module.Finite (OreLocalization S A) (OreLocalization S X) := by
  classical
  obtain ⟨g, hg⟩ := Module.Finite.fg_top (R := A) (M := X)
  refine ⟨⟨g.image (toLocalization S X), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  induction q using OreLocalization.ind with | _ x s =>
  have hx : toLocalization S X x ∈ (Submodule.span (OreLocalization S A)
      ((g.image (toLocalization S X) : Finset _) : Set (OreLocalization S X))).restrictScalars A := by
    refine Submodule.span_le_restrictScalars A (OreLocalization S A) _ ?_
    rw [Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem (hg ▸ Submodule.mem_top)
  have : x /ₒ s = ((1 : A) /ₒ s) • toLocalization S X x := by
    rw [toLocalization_apply, OreLocalization.one_div_smul, one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ hx

end Functor

section Saturation

variable {P : Type v} [AddCommGroup P] [Module (OreLocalization S A) P] [Module A P]
variable [IsScalarTower A (OreLocalization S A) P]

/-- In an `A[S⁻¹]`-module, `a ∈ A` acts as the fraction `a /ₒ 1`. -/
theorem oreDiv_one_smul_eq (a : A) (x : P) : (a /ₒ (1 : S) : OreLocalization S A) • x = a • x := by
  calc (a /ₒ (1 : S) : OreLocalization S A) • x = (a • (1 : OreLocalization S A)) • x := by
        rw [OreLocalization.one_def, smul_oreDiv_one, smul_eq_mul, mul_one]
    _ = a • x := by rw [smul_assoc, one_smul]

/-- Elements of `S` act injectively on an `A[S⁻¹]`-module. -/
theorem eq_zero_of_smul_eq_zero {s : A} (hs : s ∈ S) {x : P} (h : s • x = 0) : x = 0 := by
  have hu : IsUnit (s /ₒ (1 : S) : OreLocalization S A) := numerator_isUnit ⟨s, hs⟩
  rw [← oreDiv_one_smul_eq S] at h
  rw [← one_smul (OreLocalization S A) x, ← hu.unit.inv_mul, mul_smul]
  change hu.unit⁻¹ • ((s /ₒ (1 : S) : OreLocalization S A) • x) = 0
  rw [h, smul_zero]

variable {S} in
/-- The `S`-saturation of an `A`-submodule `K` of an `A[S⁻¹]`-module `P`: the
elements `x` with `s • x ∈ K` for some `s ∈ S`. It is the smallest
`A[S⁻¹]`-submodule containing `K`. -/
def saturation (K : Submodule A P) : Submodule (OreLocalization S A) P where
  carrier := {x | ∃ s ∈ S, s • x ∈ K}
  zero_mem' := ⟨1, S.one_mem, by rw [smul_zero]; exact K.zero_mem⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨s', hs', hy⟩
    have h := ore_eq s ⟨s', hs'⟩
    refine ⟨oreDenom s ⟨s', hs'⟩ * s, S.mul_mem (oreDenom s ⟨s', hs'⟩).2 hs, ?_⟩
    rw [smul_add]
    refine K.add_mem ?_ ?_
    · rw [mul_smul]; exact K.smul_mem _ hx
    · rw [h, mul_smul]; exact K.smul_mem _ hy
  smul_mem' := by
    rintro q x ⟨s, hs, hx⟩
    induction q using OreLocalization.ind with | _ r t =>
    have hrt : (t : A) • ((r /ₒ t) • x) = r • x := by
      rw [← oreDiv_one_smul_eq S, ← mul_smul, OreLocalization.mul_cancel, oreDiv_one_smul_eq]
    have h := ore_eq r ⟨s, hs⟩
    refine ⟨oreDenom r ⟨s, hs⟩ * t, S.mul_mem (oreDenom r ⟨s, hs⟩).2 t.2, ?_⟩
    change (oreDenom r ⟨s, hs⟩ * t : A) • ((r /ₒ t) • x) ∈ K
    rw [mul_smul, hrt, ← mul_smul, h, mul_smul]
    exact K.smul_mem _ hx

variable {S}

theorem mem_saturation {K : Submodule A P} {x : P} :
    x ∈ saturation (S := S) K ↔ ∃ s ∈ S, s • x ∈ K := Iff.rfl

theorem le_saturation (K : Submodule A P) {x : P} (hx : x ∈ K) : x ∈ saturation (S := S) K :=
  ⟨1, S.one_mem, by rwa [one_smul]⟩

theorem saturation_mono {K K' : Submodule A P} (h : K ≤ K') :
    saturation (S := S) K ≤ saturation K' := fun _ ⟨s, hs, hx⟩ => ⟨s, hs, h hx⟩

theorem saturation_inf (K K' : Submodule A P) :
    saturation (S := S) K ⊓ saturation K' ≤ saturation (K ⊓ K') := by
  rintro x ⟨⟨s, hs, hx⟩, ⟨s', hs', hx'⟩⟩
  have h := ore_eq s ⟨s', hs'⟩
  refine ⟨oreDenom s ⟨s', hs'⟩ * s, S.mul_mem (oreDenom s ⟨s', hs'⟩).2 hs, ?_, ?_⟩
  · change (oreDenom s ⟨s', hs'⟩ * s : A) • x ∈ K
    rw [mul_smul]; exact K.smul_mem _ hx
  · change (oreDenom s ⟨s', hs'⟩ * s : A) • x ∈ K'
    rw [h, mul_smul]; exact K'.smul_mem _ hx'

theorem saturation_bot : saturation (S := S) (⊥ : Submodule A P) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨s, hs, hx⟩
  exact eq_zero_of_smul_eq_zero S hs ((Submodule.mem_bot A).mp hx)

end Saturation

section UniformDimension

open AlgebraicAnalysis.Module

variable {S}
variable {N : Type v} [AddCommGroup N] [Module A N]
variable {P : Type w} [AddCommGroup P] [Module (OreLocalization S A) P] [Module A P]
variable [IsScalarTower A (OreLocalization S A) P]

/-- A direct sum of `n` nonzero `A`-submodules of `N` gives, through an
injective `A`-linear map `φ : N → P` and saturation, a direct sum of `n`
nonzero `A[S⁻¹]`-submodules of `P`. -/
theorem uniformDimGE_of_injective {φ : N →ₗ[A] P} (hφ : Function.Injective φ) {n : ℕ}
    (h : UniformDimGE A N n) : UniformDimGE (OreLocalization S A) P n := by
  obtain ⟨K, hK, hne⟩ := h
  refine ⟨fun i => saturation (S := S) ((K i).map φ), ?_, fun i h0 => ?_⟩
  · rw [iSupIndep_def] at hK ⊢
    intro i
    rw [disjoint_iff, eq_bot_iff]
    have hsup : (⨆ (j) (_ : j ≠ i), saturation (S := S) ((K j).map φ)) ≤
        saturation ((⨆ (j) (_ : j ≠ i), K j).map φ) :=
      iSup₂_le fun j hj => saturation_mono (Submodule.map_mono (le_iSup₂ (f := fun j _ => K j) j hj))
    refine (inf_le_inf_left _ hsup).trans ((saturation_inf _ _).trans ?_)
    rw [← Submodule.map_inf φ hφ, disjoint_iff.mp (hK i), Submodule.map_bot, saturation_bot]
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
    have : φ x ∈ saturation (S := S) ((K i).map φ) := le_saturation _ (Submodule.mem_map_of_mem hx)
    simp only at h0
    rw [h0, Submodule.mem_bot, ← map_zero φ] at this
    exact hx0 (hφ this)

/-- A direct sum of `n` nonzero `A[S⁻¹]`-submodules of `P` pulls back along
`φ : N → P` to a direct sum of `n` nonzero `A`-submodules of `N`, provided `φ` is
injective and every element of `P` is multiplied into the image of `φ` by an
element of `S`. -/
theorem uniformDimGE_of_essential {φ : N →ₗ[A] P} (hφ : Function.Injective φ)
    (hess : ∀ x : P, ∃ s ∈ S, s • x ∈ LinearMap.range φ) {n : ℕ}
    (h : UniformDimGE (OreLocalization S A) P n) : UniformDimGE A N n := by
  obtain ⟨K, hK, hne⟩ := h
  refine ⟨fun i => ((K i).restrictScalars A).comap φ, ?_, fun i h0 => ?_⟩
  · rw [iSupIndep_def] at hK ⊢
    intro i
    rw [Submodule.disjoint_def]
    intro y hy hy'
    have hsup : (⨆ (j) (_ : j ≠ i), ((K j).restrictScalars A).comap φ) ≤
        ((⨆ (j) (_ : j ≠ i), K j).restrictScalars A).comap φ :=
      iSup₂_le fun j hj => Submodule.comap_mono
        ((Submodule.restrictScalars_le A).mpr (le_iSup₂ (f := fun j _ => K j) j hj))
    have := (Submodule.disjoint_def.mp (hK i)) (φ y) hy (hsup hy')
    exact hφ (this.trans (map_zero φ).symm)
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
    obtain ⟨s, hs, y, hy⟩ := hess x
    have hyK : y ∈ ((K i).restrictScalars A).comap φ := by
      change φ y ∈ (K i).restrictScalars A
      rw [hy]
      exact Submodule.smul_mem _ s ((Submodule.restrictScalars_mem A (K i) x).mpr hx)
    simp only at h0
    rw [h0, Submodule.mem_bot] at hyK
    rw [hyK, map_zero] at hy
    exact hx0 (eq_zero_of_smul_eq_zero S hs hy.symm)

/-- **Uniform dimension is preserved by localization** (McConnell–Robson 2.2.13).
Let `φ : N → P` be an injective `A`-linear map into an `A[S⁻¹]`-module such that
every `x ∈ P` has some `s ∈ S` with `s • x` in the image of `φ`. Then `N`
contains a direct sum of `n` nonzero `A`-submodules if and only if `P` contains a
direct sum of `n` nonzero `A[S⁻¹]`-submodules. -/
theorem uniformDimGE_iff_of_injective {φ : N →ₗ[A] P} (hφ : Function.Injective φ)
    (hess : ∀ x : P, ∃ s ∈ S, s • x ∈ LinearMap.range φ) {n : ℕ} :
    UniformDimGE A N n ↔ UniformDimGE (OreLocalization S A) P n :=
  ⟨uniformDimGE_of_injective hφ, uniformDimGE_of_essential hφ hess⟩

end UniformDimension

end AlgebraicAnalysis.OreModule
