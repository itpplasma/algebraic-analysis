module
public import AlgebraicAnalysis.Module.DualSeparation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Finite critical dual separation

Restriction of germ Hom is left exact. The scalars are the target's germ
endomorphisms acting on the left by postcomposition.

Original proofs of the interfaces in generalized-stafford's
`.lake/research/active/formal-scope-BC.md`, step 7, and
`docs/categorical-localization.md`, §1; no downstream code is extracted.
-/

universe u v w z

open scoped Classical
namespace Module.Germ
variable {R : Type u} [Ring R] {e : ℕ}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {C : Type z} [AddCommGroup C] [Module R C]

namespace PartialHom

/-- A partial map to a critical module descends through a quotient when its
restriction to the kernel vanishes. -/
theorem exists_factor_mkQ_of_critical (hC : Module.Critical R e C)
    (U : Submodule R M) (f : PartialHom R e M C)
    (hf : f.comp (ofLinearMap U.subtype) = 0) :
    ∃ g : PartialHom R e (M ⧸ U) C, f = g.comp (ofLinearMap U.mkQ) := by
  induction f using Quotient.inductionOn with | _ f =>
  have hz := (mk_eq_zero_iff_of_critical hC
    (f.comp (.ofLinearMap U.subtype))).mp hf
  let q := U.mkQ.submoduleMap f.val.domain
  have hq : Function.Surjective q := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk : LinearMap.ker q ≤ LinearMap.ker f.val.toFun := by
    intro x hx
    have hxu : x.val ∈ U := (Submodule.Quotient.mk_eq_zero U).mp
      (congrArg Subtype.val hx)
    have hd : (⟨x.val, hxu⟩ : U) ∈
        (f.comp (.ofLinearMap U.subtype)).val.domain := by
      apply (Representative.mem_pullback _ _ Submodule.mem_top).mpr
      exact x.property
    exact LinearMap.congr_fun hz ⟨⟨x.val, hxu⟩, hd⟩
  let b : f.val.domain.map U.mkQ →ₗ[R] C :=
    ((LinearMap.ker q).liftQ f.val.toFun hk).comp
      (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hb (x : f.val.domain) : b (q x) = f.val x := by
    dsimp [b]
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  let g : Representative R e (M ⧸ U) C :=
    ⟨⟨f.val.domain.map U.mkQ, b⟩, f.property.map _ U.mkQ_surjective⟩
  refine ⟨mk g, Quotient.sound ?_⟩
  refine ⟨f.val.domain, f.property, le_rfl, ?_, ?_⟩
  · intro x hx
    exact (Representative.mem_pullback _ _ Submodule.mem_top).mpr ⟨x, hx, rfl⟩
  · intro x
    exact (hb x).symm

end PartialHom
namespace Hom

/-- Pull a normalized germ back to the original source, retaining the reduced
target. Surjectivity of the radical quotient makes this operation injective. -/
def pullSource (f : Hom R e M C) :
    PartialHom R e M (C ⧸ smallRadical R e C) :=
  PartialHom.comp f (PartialHom.ofLinearMap (smallRadical R e M).mkQ)

theorem pullSource_injective : Function.Injective
    (pullSource (R := R) (e := e) (M := M) (C := C)) := by
  intro f g h
  apply PartialHom.Epic.right_cancel (f := PartialHom.ofLinearMap
    (smallRadical R e M).mkQ) _ f g h
  rw [PartialHom.epic_ofLinearMap_iff]
  rw [LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)]
  exact small_of_subsingleton e

theorem pullSource_comp_ofLinearMap (f : Hom R e M C) (a : N →ₗ[R] M) :
    pullSource (comp f (ofLinearMap a)) =
      PartialHom.comp (pullSource f) (PartialHom.ofLinearMap a) := by
  unfold pullSource comp ofLinearMap
  simp only [PartialHom.comp_assoc, ← PartialHom.ofLinearMap_comp]
  rfl

@[simp] theorem pullSource_zero : pullSource (0 : Hom R e M C) = 0 :=
  PartialHom.zero_comp _

set_option backward.isDefEq.respectTransparency false in
/-- Every partial map into the reduced target defines a normalized
germ with the same pullback to the original source. -/
theorem exists_pullSource [IsNoetherian R M] [IsNoetherian R C]
    (f : PartialHom R e M (C ⧸ smallRadical R e C)) :
    ∃ g : Hom R e M C, pullSource g = f := by
  induction f using Quotient.inductionOn with | _ f =>
  let p : Pair R e M C :=
    ⟨f.val.domain, f.property, smallRadical R e C, small_smallRadical, f.val.toFun⟩
  refine ⟨p.toHom, Quotient.sound ?_⟩
  refine ⟨f.val.domain, f.property, ?_, le_rfl, ?_⟩
  · intro x hx
    exact (Representative.mem_pullback _ _ Submodule.mem_top).mpr ⟨x, hx, rfl⟩
  · intro x
    change p.normalize.val (p.domainMap x) = f.val x
    rw [Pair.normalize_apply]
    change Submodule.mapQ (smallRadical R e C) (smallRadical R e C)
      LinearMap.id le_rfl (f.val x) = f.val x
    rw [Submodule.mapQ_id]
    rfl

/-- Left exactness of germ Hom along an ordinary submodule, for a critical
target. The factorization is unique, since the quotient germ is epic. -/
theorem comp_subtype_eq_zero_iff [IsNoetherian R M] [IsNoetherian R C]
    (hC : Module.Critical R e C) (U : Submodule R M) (f : Hom R e M C) :
    comp f (ofLinearMap U.subtype) = 0 ↔
      ∃ g : Hom R e (M ⧸ U) C, f = comp g (ofLinearMap U.mkQ) := by
  constructor
  · intro hf
    have hz : (pullSource f).comp (PartialHom.ofLinearMap U.subtype) = 0 := by
      rw [← pullSource_comp_ofLinearMap, hf, pullSource_zero]
    obtain ⟨g, hg⟩ := PartialHom.exists_factor_mkQ_of_critical
      (critical_quotient_smallRadical hC) U (pullSource f) hz
    obtain ⟨g, rfl⟩ := exists_pullSource g
    refine ⟨g, pullSource_injective ?_⟩
    rw [pullSource_comp_ofLinearMap]
    exact hg
  · rintro ⟨g, rfl⟩
    rw [comp_assoc, ← ofLinearMap_comp]
    have hz : U.mkQ.comp U.subtype = 0 := by ext x; simp
    rw [hz, ofLinearMap_zero]
    exact PartialHom.comp_zero g

/-- Precomposition is linear over the target's germ endomorphism ring. -/
def precompLinear (x : Hom R e N M) :
    Hom R e M C →ₗ[End R e C] Hom R e N C where
  toFun f := comp f x
  map_add' f g := add_comp f g x
  map_smul' a f := comp_assoc a f x

/-- Restriction to a submodule as a left Schur-linear map. -/
def restrictLinear (U : Submodule R M) :
    Hom R e M C →ₗ[End R e C] Hom R e U C :=
  precompLinear (ofLinearMap U.subtype)

/-- Pullback along the quotient as a left Schur-linear map. -/
def quotientLinear (U : Submodule R M) :
    Hom R e (M ⧸ U) C →ₗ[End R e C] Hom R e M C :=
  precompLinear (ofLinearMap U.mkQ)

/-- The left-exact sequence `0 → Hom(M/U,C) → Hom(M,C) → Hom(U,C)`. -/
theorem range_quotientLinear_eq_ker_restrictLinear
    [IsNoetherian R M] [IsNoetherian R C]
    (hC : Module.Critical R e C) (U : Submodule R M) :
    LinearMap.range (quotientLinear (C := C) (e := e) U) =
      LinearMap.ker (restrictLinear (C := C) (e := e) U) := by
  ext f
  change (∃ g, comp g (ofLinearMap U.mkQ) = f) ↔
    comp f (ofLinearMap U.subtype) = 0
  rw [comp_subtype_eq_zero_iff hC]
  constructor <;> rintro ⟨g, hg⟩ <;> exact ⟨g, hg.symm⟩

/-- Surjective ordinary maps remain epic after normalization. -/
theorem epic_ofLinearMap_of_surjective (a : N →ₗ[R] M)
    (ha : Function.Surjective a) : Epic (ofLinearMap (e := e) a) := by
  apply (PartialHom.epic_ofLinearMap_iff _).mpr
  have hr : Function.Surjective (reducedMap (e := e) a) := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (smallRadical R e M) y
    obtain ⟨x, rfl⟩ := ha y
    exact ⟨(smallRadical R e N).mkQ x, rfl⟩
  rw [LinearMap.range_eq_top.mpr hr]
  exact small_of_subsingleton e

/-- The first arrow in the left-exact Schur sequence is injective. -/
theorem quotientLinear_injective (U : Submodule R M) :
    Function.Injective (quotientLinear (C := C) (e := e) U) :=
  fun _ _ h => (epic_ofLinearMap_of_surjective U.mkQ U.mkQ_surjective).right_cancel _ _ h

/-- A linear equivalence of sources induces a Schur-linear equivalence. -/
def precompEquiv (a : M ≃ₗ[R] N) :
    Hom R e N C ≃ₗ[End R e C] Hom R e M C where
  __ := precompLinear (ofLinearMap a.toLinearMap)
  invFun f := comp f (ofLinearMap a.symm.toLinearMap)
  left_inv f := by
    change comp (comp f _) _ = f
    rw [comp_assoc, ← ofLinearMap_comp, a.comp_symm,
      ofLinearMap_id, comp_id]
  right_inv f := by
    change comp (comp f _) _ = f
    rw [comp_assoc, ← ofLinearMap_comp, a.symm_comp,
      ofLinearMap_id, comp_id]

/-- Germ Hom out of a small source vanishes. -/
theorem subsingleton_of_small (hM : Small R e M) :
    Subsingleton (Hom R e M C) := by
  have ht : smallRadical R e M = ⊤ := by
    apply top_unique
    apply le_smallRadical
    exact (small_linearEquiv_iff e (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M)).mpr hM
  have : Subsingleton (M ⧸ smallRadical R e M) := by rw [ht]; infer_instance
  constructor
  intro f g
  induction f using Quotient.inductionOn with | _ f =>
  induction g using Quotient.inductionOn with | _ g =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  have hxf : (⟨x, hx⟩ : f.val.domain) = 0 := Subsingleton.elim _ _
  have hxg : (⟨x, hy⟩ : g.val.domain) = 0 := Subsingleton.elim _ _
  rw [hxf, hxg]
  exact f.val.toFun.map_zero.trans g.val.toFun.map_zero.symm

/-- Finiteness and the dimension inequality for one left-exact Schur sequence. -/
theorem finite_finrank_le_of_submodule [IsNoetherian R M] [IsNoetherian R C]
    (hC : Module.Critical R e C) (U : Submodule R M)
    [Module.Finite (End R e C) (Hom R e U C)]
    [Module.Finite (End R e C) (Hom R e (M ⧸ U) C)] :
    letI := End.divisionRing hC
    Module.Finite (End R e C) (Hom R e M C) ∧
      Module.finrank (End R e C) (Hom R e M C) ≤
        Module.finrank (End R e C) (Hom R e U C) +
          Module.finrank (End R e C) (Hom R e (M ⧸ U) C) := by
  letI := End.divisionRing hC
  let a := quotientLinear (C := C) (e := e) U
  let b := restrictLinear (C := C) (e := e) U
  have hr : LinearMap.range a = LinearMap.ker b :=
    range_quotientLinear_eq_ker_restrictLinear hC U
  haveI : Module.Finite (End R e C) (LinearMap.ker b) := by
    rw [← hr]
    infer_instance
  haveI : Module.Finite (End R e C) (Hom R e M C) :=
    Module.Finite.of_exact (f := (LinearMap.ker b).subtype) (g := b.rangeRestrict)
      (LinearMap.exact_iff.mpr (by ext x; simp))
      (by rintro ⟨y, x, rfl⟩; exact ⟨x, rfl⟩)
  refine ⟨inferInstance, ?_⟩
  have hk : Module.finrank (End R e C) (LinearMap.ker b) ≤
      Module.finrank (End R e C) (Hom R e (M ⧸ U) C) := by
    rw [← hr]
    exact a.finrank_range_le
  have hb := (LinearMap.range b).finrank_le
  have he := b.finrank_range_add_finrank_ker
  omega

end Hom

private noncomputable def schurWeight
    (s : RelSeries {(p, q) | Module.CriticalStep R e M p q}) : ℕ := by
  classical
  exact ∑ i : Fin s.length,
    if Small R e (s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype) then 0 else 1

set_option backward.isDefEq.respectTransparency false in
private theorem schurWeight_snoc
    (s : RelSeries {(p, q) | Module.CriticalStep R e M p q}) (b : Submodule R M)
    (h : Module.CriticalStep R e M s.last b) :
    schurWeight (s.snoc b h) = schurWeight s +
      if Small R e (b ⧸ s.last.comap b.subtype) then 0 else 1 := by
  classical
  unfold schurWeight
  change (∑ i : Fin (s.length + 1),
    if Small R e ((s.snoc b h) i.succ ⧸
      ((s.snoc b h) i.castSucc).comap ((s.snoc b h) i.succ).subtype) then 0 else 1) = _
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hi : (Fin.castSucc i).succ = Fin.castSucc i.succ := rfl
    rw [hi, RelSeries.snoc_castSucc, RelSeries.snoc_castSucc]
  · rw [RelSeries.snoc_castSucc]
    change (if Small R e ((s.snoc b h) (Fin.last (s.length + 1)) ⧸
      s.last.comap ((s.snoc b h) (Fin.last (s.length + 1))).subtype) then 0 else 1) = _
    rw [RelSeries.last_snoc']

/-- Every surviving factor at the ceiling is critical at that ceiling. -/
theorem critical_of_criticalStep_not_small {p q : Submodule R M}
    (h : Module.CriticalStep R e M p q)
    (hs : ¬Small R e (q ⧸ p.comap q.subtype)) :
    Module.Critical R e (q ⧸ p.comap q.subtype) := by
  obtain ⟨d, hd, hc⟩ := h.2
  have he : e ≤ d := by
    by_contra he
    exact hs ((show Small R (d + 1) (q ⧸ p.comap q.subtype) from hc.devLE).mono
      (Nat.succ_le_of_lt (Nat.lt_of_not_ge he)))
  have hde : d = e := le_antisymm hd he
  subst d
  exact hc

namespace Hom

private theorem finite_finrank_le_series [IsNoetherian R M] [IsNoetherian R C]
    (hC : Module.Critical R e C)
    (s : RelSeries {(p, q) | Module.CriticalStep R e M p q})
    (hs : Small R e s.head) :
    letI := End.divisionRing hC
    Module.Finite (End R e C) (Hom R e s.last C) ∧
      Module.finrank (End R e C) (Hom R e s.last C) ≤ schurWeight s := by
  classical
  letI := End.divisionRing hC
  induction s using RelSeries.inductionOn' with
  | singleton p =>
    rw [RelSeries.last_singleton]
    change Small R e p at hs
    haveI := subsingleton_of_small (C := C) hs
    exact ⟨inferInstance, by simp [schurWeight, Module.finrank_zero_of_subsingleton]⟩
  | snoc s b h ih =>
    rw [RelSeries.head_snoc] at hs
    rw [RelSeries.last_snoc]
    obtain ⟨hfin, hdim⟩ := ih hs
    letI := hfin
    let U := s.last.comap b.subtype
    let a : U ≃ₗ[R] s.last := Submodule.comapSubtypeEquivOfLe h.1
    let t := precompEquiv (C := C) (e := e) a
    haveI : Module.Finite (End R e C) (Hom R e U C) :=
      Module.Finite.of_surjective t.toLinearMap t.surjective
    have hu : Module.finrank (End R e C) (Hom R e U C) ≤ schurWeight s := by
      rw [← t.finrank_eq]
      exact hdim
    have hfactor : Module.Finite (End R e C) (Hom R e (b ⧸ U) C) ∧
        Module.finrank (End R e C) (Hom R e (b ⧸ U) C) ≤
          if Small R e (b ⧸ U) then 0 else 1 := by
      by_cases hf : Small R e (b ⧸ U)
      · haveI := subsingleton_of_small (C := C) hf
        exact ⟨inferInstance, by simp [hf, Module.finrank_zero_of_subsingleton]⟩
      · have hc := critical_of_criticalStep_not_small h hf
        exact ⟨finite_of_critical hc hC, by simpa [hf] using finrank_le_one_of_critical hc hC⟩
    letI := hfactor.1
    obtain ⟨hf, hd⟩ := finite_finrank_le_of_submodule hC U
    refine ⟨hf, ?_⟩
    rw [schurWeight_snoc]
    exact hd.trans (Nat.add_le_add hu hfactor.2)

/-- A finite critical filtration bounds every critical Schur space by its
number of surviving factors. -/
theorem finite_finrank_le_topLength [IsNoetherian R M] [IsNoetherian R C]
    (hC : Module.Critical R e C) (F : Module.CriticalFiltration R e M) :
    letI := End.divisionRing hC
    Module.Finite (End R e C) (Hom R e M C) ∧
      Module.finrank (End R e C) (Hom R e M C) ≤ F.topLength e := by
  letI := End.divisionRing hC
  have hs : Small R e F.toRelSeries.head := by rw [F.head_eq_bot]; exact small_of_subsingleton e
  have h := finite_finrank_le_series hC F.toRelSeries hs
  change Module.Finite (End R e C) (Hom R e F.toRelSeries.last C) ∧
    Module.finrank (End R e C) (Hom R e F.toRelSeries.last C) ≤ F.topLength e at h
  rw [F.last_eq_top] at h
  letI := h.1
  let t := precompEquiv (C := C) (e := e) (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M)
  refine ⟨Module.Finite.of_surjective t.symm.toLinearMap t.symm.surjective, ?_⟩
  rw [t.finrank_eq]
  exact h.2

/-- Finite-deviation Noetherian sources have finite critical Schur spaces. -/
theorem finite_of_devLE [IsNoetherian R M] [IsNoetherian R C]
    (hM : Module.DevLE R e M) (hC : Module.Critical R e C) :
    Module.Finite (End R e C) (Hom R e M C) := by
  obtain ⟨F⟩ := hM.nonempty_criticalFiltration
  exact (finite_finrank_le_topLength hC F).1

set_option backward.isDefEq.respectTransparency false in
private theorem exists_nonzero_factor_series [IsNoetherian R M] [IsNoetherian R C]
    (hC : Module.Critical R e C)
    (s : RelSeries {(p, q) | Module.CriticalStep R e M p q})
    (hs : Small R e s.head) (f : Hom R e s.last C) (hf : f ≠ 0) :
    ∃ i : Fin s.length,
      ¬Small R e (s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype) ∧
        ∃ g : Hom R e (s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype) C,
          g ≠ 0 := by
  classical
  induction s using RelSeries.inductionOn' with
  | singleton p =>
    revert f hf
    rw [RelSeries.last_singleton]
    intro f hf
    change Small R e p at hs
    haveI := subsingleton_of_small (C := C) hs
    exact False.elim (hf (Subsingleton.elim _ _))
  | snoc s b h ih =>
    rw [RelSeries.head_snoc] at hs
    revert f hf
    rw [RelSeries.last_snoc]
    intro f hf
    let U := s.last.comap b.subtype
    let a : U ≃ₗ[R] s.last := Submodule.comapSubtypeEquivOfLe h.1
    let t := precompEquiv (C := C) (e := e) a
    by_cases hz : comp f (ofLinearMap U.subtype) = 0
    · obtain ⟨g, hg⟩ := (comp_subtype_eq_zero_iff hC U f).mp hz
      have hgn : g ≠ 0 := by
        intro he
        apply hf
        rw [hg, he]
        exact PartialHom.zero_comp _
      have hns : ¬Small R e (b ⧸ U) := by
        intro hsmall
        haveI := subsingleton_of_small (C := C) hsmall
        exact hgn (Subsingleton.elim _ _)
      refine ⟨Fin.last s.length, ?_⟩
      change ¬Small R e ((s.snoc b h) (Fin.last (s.length + 1)) ⧸
        ((s.snoc b h) (Fin.castSucc (Fin.last s.length))).comap
          ((s.snoc b h) (Fin.last (s.length + 1))).subtype) ∧
        ∃ g : Hom R e ((s.snoc b h) (Fin.last (s.length + 1)) ⧸
          ((s.snoc b h) (Fin.castSucc (Fin.last s.length))).comap
            ((s.snoc b h) (Fin.last (s.length + 1))).subtype) C, g ≠ 0
      rw [RelSeries.snoc_castSucc, RelSeries.last_snoc']
      exact ⟨hns, g, hgn⟩
    · have ht : t.symm (comp f (ofLinearMap U.subtype)) ≠ 0 := by
        intro he
        apply hz
        exact t.symm.injective (he.trans (map_zero _).symm)
      obtain ⟨i, hi⟩ := ih hs _ ht
      refine ⟨i.castSucc, ?_⟩
      have he : i.castSucc.succ = i.succ.castSucc := rfl
      change ¬Small R e ((s.snoc b h) i.castSucc.succ ⧸
        ((s.snoc b h) i.castSucc.castSucc).comap ((s.snoc b h) i.castSucc.succ).subtype) ∧
        ∃ g : Hom R e ((s.snoc b h) i.castSucc.succ ⧸
          ((s.snoc b h) i.castSucc.castSucc).comap ((s.snoc b h) i.castSucc.succ).subtype) C, g ≠ 0
      rw [he, RelSeries.snoc_castSucc, RelSeries.snoc_castSucc]
      exact hi

/-- A nonzero critical Schur Hom detects one of the surviving factors of
any chosen critical filtration. -/
theorem exists_factor_hom_of_ne_zero [IsNoetherian R M] [IsNoetherian R C]
    (hC : Module.Critical R e C) (F : Module.CriticalFiltration R e M)
    (f : Hom R e M C) (hf : f ≠ 0) :
    ∃ i : Fin F.length, ¬Small R e (F.Factor i) ∧
      ∃ g : Hom R e (F.Factor i) C, g ≠ 0 := by
  have hs : Small R e F.toRelSeries.head := by rw [F.head_eq_bot]; exact small_of_subsingleton e
  have h := exists_nonzero_factor_series hC F.toRelSeries hs
  rw [F.last_eq_top] at h
  let t := precompEquiv (C := C) (e := e)
    (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M)
  exact h (t f) (fun he => hf (t.injective (he.trans (map_zero _).symm)))

end Hom
end Module.Germ

namespace Module.CriticalFiltration
variable {R : Type u} [Ring R] {e : ℕ}
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The finite index family of critical factors surviving at the ceiling.
Repeated isomorphic factors may occur. -/
abbrev TopIndex (F : CriticalFiltration R e M) :=
  {i : Fin F.length // ¬Small R e (F.Factor i)}

/-- The critical module representing a retained type. -/
abbrev TopFactor (F : CriticalFiltration R e M) (i : F.TopIndex) := F.Factor i.val

/-- Each retained type is critical at the common ceiling. -/
theorem topFactor_critical (F : CriticalFiltration R e M) (i : F.TopIndex) :
    Critical R e (F.TopFactor i) :=
  Germ.critical_of_criticalStep_not_small (F.step i.val) i.property

/-- The number of retained indices is exactly the top length. -/
theorem card_topIndex (F : CriticalFiltration R e M) :
    Fintype.card F.TopIndex = F.topLength e := by
  classical
  simp only [TopIndex, Fintype.card_subtype, topLength,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : Small R e (F.Factor i) <;> simp [hs]

end Module.CriticalFiltration

namespace Module.Germ.Hom
variable {R : Type u} [Ring R] {e : ℕ}
variable {M : Type v} [AddCommGroup M] [Module R M] [IsNoetherian R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {C : Type z} [AddCommGroup C] [Module R C] [IsNoetherian R C]

/-- Every critical target with nonzero dual Hom is germ-isomorphic to a
retained factor. This identifies the finite list of critical types. -/
theorem exists_topFactor_iso_of_ne_zero (hC : Module.Critical R e C)
    (F : Module.CriticalFiltration R e M) (f : Hom R e M C) (hf : f ≠ 0) :
    ∃ i : F.TopIndex, ∃ g : Hom R e (F.TopFactor i) C,
      ∃ a : Hom R e C (F.TopFactor i), comp a g = id ∧ comp g a = id := by
  obtain ⟨i, hi, g, hg⟩ := exists_factor_hom_of_ne_zero hC F f hf
  let j : F.TopIndex := ⟨i, hi⟩
  obtain ⟨a, hag, hga⟩ := exists_inverse_of_critical (F.topFactor_critical j) hC g hg
  exact ⟨j, g, a, hag, hga⟩

/-- The Schur spaces associated to the retained types are finite and bounded
by the number of surviving filtration factors. -/
theorem topFactor_finite_finrank_le (F : Module.CriticalFiltration R e M)
    (i : F.TopIndex) :
    letI := End.divisionRing (F.topFactor_critical i)
    Module.Finite (End R e (F.TopFactor i)) (Hom R e M (F.TopFactor i)) ∧
      Module.finrank (End R e (F.TopFactor i)) (Hom R e M (F.TopFactor i)) ≤
        F.topLength e :=
  finite_finrank_le_topLength (F.topFactor_critical i) F

/-- Finite critical dual separation. A germ with arbitrary source is epic
modulo small modules exactly when precomposition is injective on the finitely
many critical Schur spaces supplied by a critical filtration. -/
theorem epic_iff_injective_comp_topFactors (hM : Module.DevLE R e M)
    (F : Module.CriticalFiltration R e M) (x : Hom R e N M) :
    Epic x ↔ ∀ i : F.TopIndex, Function.Injective
      (fun h : Hom R e M (F.TopFactor i) => comp h x) := by
  classical
  refine ⟨fun hx _ _ _ he => hx.right_cancel _ _ he, ?_⟩
  intro hinj
  by_contra hx
  induction x using Quotient.inductionOn with | _ x =>
  have hns : ¬Small R e ((M ⧸ smallRadical R e M) ⧸ x.val.toFun.range) := hx
  have hd := ((hM.quotient (smallRadical R e M)).quotient x.val.toFun.range)
  obtain ⟨p, hp⟩ := hd.exists_critical_quotient hns
  let Q := ((M ⧸ smallRadical R e M) ⧸ x.val.toFun.range) ⧸ p
  let b : (M ⧸ smallRadical R e M) →ₗ[R] Q := p.mkQ.comp x.val.toFun.range.mkQ
  let k : M →ₗ[R] Q := b.comp (smallRadical R e M).mkQ
  have hks : Function.Surjective k :=
    p.mkQ_surjective.comp (x.val.toFun.range.mkQ_surjective.comp
      (Submodule.mkQ_surjective _))
  have hkn : ofLinearMap (e := e) k ≠ 0 := by
    intro hz
    have hs := (ofLinearMap_eq_zero_iff k).mp hz
    rw [LinearMap.range_eq_top.mpr hks] at hs
    exact hp.not_small (hs.of_surjective (⊤ : Submodule R Q).subtype
      (fun y => ⟨⟨y, Submodule.mem_top⟩, rfl⟩))
  have hkred : reducedMap (e := e) k = (smallRadical R e Q).mkQ.comp b := by
    apply LinearMap.ext
    intro y
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (smallRadical R e M) y
    rfl
  have hkill : comp (ofLinearMap k) (PartialHom.mk x) = 0 := by
    apply Quotient.sound
    apply Representative.rel_of_eq
    intro y hy _
    change reducedMap k (x.val ⟨y, x.pullback_le _ hy⟩) = 0
    rw [hkred]
    have hz : x.val.toFun.range.mkQ (x.val ⟨y, x.pullback_le _ hy⟩) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
    change (smallRadical R e Q).mkQ (p.mkQ (x.val.toFun.range.mkQ _)) = 0
    rw [hz, map_zero, map_zero]
  obtain ⟨i, g, a, hag, hga⟩ := exists_topFactor_iso_of_ne_zero hp F (ofLinearMap k) hkn
  let h : Hom R e M (F.TopFactor i) := comp a (ofLinearMap k)
  have hne : h ≠ 0 := by
    intro hz
    have he := congrArg (fun t => comp g t) hz
    change comp g (comp a (ofLinearMap k)) = comp g 0 at he
    rw [← comp_assoc, hga, id_comp] at he
    exact hkn (he.trans (PartialHom.comp_zero _))
  apply hne
  apply hinj i
  change comp (comp a (ofLinearMap k)) (PartialHom.mk x) = comp 0 (PartialHom.mk x)
  rw [comp_assoc, hkill]
  exact (PartialHom.comp_zero _).trans (PartialHom.zero_comp _).symm

end Module.Germ.Hom
