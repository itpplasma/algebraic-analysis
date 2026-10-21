module
public import AlgebraicAnalysis.Module.Germ
public import AlgebraicAnalysis.Module.Critical
public import Mathlib.Algebra.Field.Basic

@[expose] public section

/-!
# Schur's lemma for critical germs

Multiplication of germ endomorphisms is composition, with the left factor
applied last. All module structures use left scalars; right modules are
represented using the opposite ring.

These are new proofs of the interfaces in generalized-stafford's
`docs/categorical-localization.md`, §§1–2, and
`.lake/research/active/formal-scope-BC.md`, steps 5–6; no Lean declarations
are extracted or duplicated from a downstream repository.
-/

universe u v w z

namespace Module
namespace Germ

variable {R : Type u} [Ring R] {e : ℕ}
variable {C : Type v} [AddCommGroup C] [Module R C]
variable {D : Type w} [AddCommGroup D] [Module R D]

/-- A nonzero map between critical modules of the same dimension is injective. -/
theorem critical_injective_of_ne_zero (hC : Critical R e C) (hD : Critical R e D)
    (f : C →ₗ[R] D) (hf : f ≠ 0) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hk
  have hs : Small R e f.range :=
    (small_linearEquiv_iff e f.quotKerEquivRange).mp (hC.small_quotient _ hk)
  have hr : f.range = ⊥ := by
    by_contra hr
    exact hD.not_small_submodule hr hs
  exact hf (LinearMap.range_eq_bot.mp hr)

namespace PartialHom

/-- For a critical target, a representative is zero as a germ exactly when
its underlying map is zero. -/
theorem mk_eq_zero_iff_of_critical (hD : Critical R e D)
    (f : Representative R e C D) : mk f = 0 ↔ f.val.toFun = 0 := by
  constructor
  · intro hf
    obtain ⟨U, hU, hUf, _, he⟩ := Quotient.exact hf
    have hk : U ≤ (LinearMap.ker f.val.toFun).map f.val.domain.subtype := by
      intro x hx
      exact ⟨⟨x, hUf hx⟩, he ⟨x, hx⟩, rfl⟩
    have hd := (hU.mono hk).comap f.val.domain.subtype
    rw [Submodule.comap_map_eq_of_injective Subtype.val_injective] at hd
    have hs := (small_linearEquiv_iff e f.val.toFun.quotKerEquivRange).mp hd
    have hr : f.val.toFun.range = ⊥ := by
      by_contra hr
      exact hD.not_small_submodule hr hs
    exact LinearMap.range_eq_bot.mp hr
  · intro hf
    apply Quotient.sound
    apply Representative.rel_of_eq
    intro x hx hy
    change f.val.toFun _ = 0
    rw [hf]; rfl

/-- A nonzero germ into a critical module has dense range. -/
theorem epic_of_ne_zero_of_critical (hD : Critical R e D)
    (f : PartialHom R e C D) (hf : f ≠ 0) : Epic f := by
  induction f using Quotient.inductionOn with | _ f =>
  apply hD.small_quotient
  intro hr
  exact hf ((mk_eq_zero_iff_of_critical hD f).mpr (LinearMap.range_eq_bot.mp hr))

/-- Nonzero germs between critical modules admit two-sided inverses. -/
theorem exists_inverse_of_critical (hC : Critical R e C) (hD : Critical R e D)
    (f : PartialHom R e C D) (hf : f ≠ 0) :
    ∃ g : PartialHom R e D C,
      g.comp f = ofLinearMap LinearMap.id ∧ f.comp g = ofLinearMap LinearMap.id := by
  induction f using Quotient.inductionOn with | _ f =>
  have hd : f.val.domain ≠ ⊥ := by
    intro hd
    apply hf
    apply (mk_eq_zero_iff_of_critical hD f).mpr
    ext x
    have hx : x = 0 := Subtype.ext (hd.le x.property)
    rw [hx, map_zero, LinearMap.zero_apply]
  have hi := critical_injective_of_ne_zero (hC.submodule _ hd) hD f.val.toFun
    (fun hz => hf ((mk_eq_zero_iff_of_critical hD f).mpr hz))
  let a := LinearEquiv.ofInjective f.val.toFun hi
  let g : Representative R e D C :=
    ⟨⟨f.val.toFun.range, f.val.domain.subtype.comp a.symm.toLinearMap⟩,
      epic_of_ne_zero_of_critical hD (mk f) hf⟩
  refine ⟨mk g, ?_, ?_⟩
  · apply Quotient.sound
    apply Representative.rel_of_eq
    intro x hx hy
    have hx' : x ∈ f.val.domain := f.pullback_le _ hx
    exact congrArg Subtype.val (a.symm_apply_apply ⟨x, hx'⟩)
  · apply Quotient.sound
    apply Representative.rel_of_eq
    intro x hx hy
    have hx' : x ∈ f.val.toFun.range := g.pullback_le _ hx
    exact congrArg Subtype.val (a.apply_symm_apply ⟨x, hx'⟩)

end PartialHom

/-- Normalizing a Noetherian critical module preserves criticality. -/
theorem critical_quotient_smallRadical (hC : Critical R e C) [IsNoetherian R C] :
    Critical R e (C ⧸ smallRadical R e C) :=
  hC.of_linearEquiv ((smallRadical R e C).quotEquivOfEqBot hC.smallRadical_eq_bot).symm

namespace Hom

/-- Schur's inverse theorem for normalized germs. -/
theorem exists_inverse_of_critical [IsNoetherian R C] [IsNoetherian R D]
    (hC : Critical R e C) (hD : Critical R e D) (f : Hom R e C D) (hf : f ≠ 0) :
    ∃ g : Hom R e D C, comp g f = id ∧ comp f g = id :=
  PartialHom.exists_inverse_of_critical (critical_quotient_smallRadical hC)
    (critical_quotient_smallRadical hD) f hf

end Hom

/-- Germ endomorphisms, with composition as multiplication. -/
abbrev End (R : Type u) [Ring R] (e : ℕ) (C : Type v)
    [AddCommGroup C] [Module R C] := Hom R e C C

namespace End

instance : Ring (End R e C) where
  one := Hom.id
  mul := Hom.comp
  mul_assoc := Hom.comp_assoc
  one_mul := Hom.id_comp
  mul_one := Hom.comp_id
  left_distrib := Hom.comp_add
  right_distrib := Hom.add_comp
  zero_mul := PartialHom.zero_comp
  mul_zero := PartialHom.comp_zero

/-- The Schur division ring of a Noetherian critical module. This is an
explicit structure because criticality is a proposition, not a typeclass. -/
noncomputable abbrev divisionRing [IsNoetherian R C] (hC : Critical R e C) :
    DivisionRing (End R e C) := by
  letI : Nontrivial (End R e C) := by
    apply nontrivial_of_ne (1 : End R e C) 0
    intro h
    have hz : Hom.ofLinearMap (e := e) (LinearMap.id : C →ₗ[R] C) = 0 := by
      rw [Hom.ofLinearMap_id]
      exact h
    have hs := (Hom.ofLinearMap_eq_zero_iff _).mp hz
    rw [LinearMap.range_id] at hs
    exact hC.not_small (hs.of_surjective (⊤ : Submodule R C).subtype
      (fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩))
  exact DivisionRing.ofIsUnitOrEqZero fun f => by
    by_cases hf : f = 0
    · exact Or.inr hf
    · obtain ⟨g, hgf, hfg⟩ := Hom.exists_inverse_of_critical hC hC f hf
      exact Or.inl ⟨⟨f, g, hfg, hgf⟩, rfl⟩

end End

namespace Hom

@[simp] theorem ofLinearMap_zero : ofLinearMap (e := e) (0 : C →ₗ[R] D) = 0 := by
  have hz : reducedMap (e := e) (0 : C →ₗ[R] D) = 0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (smallRadical R e C) x
    rfl
  unfold ofLinearMap
  rw [hz]
  rfl

/-- Composition makes every germ Hom into a left module over target endomorphisms. -/
instance : Module (End R e D) (Hom R e C D) where
  smul := comp
  one_smul := id_comp
  mul_smul := comp_assoc
  smul_add := comp_add
  smul_zero := PartialHom.comp_zero
  add_smul := add_comp
  zero_smul := PartialHom.zero_comp

end Hom

namespace End

/-- Multiplication by a central scalar, as a linear map. -/
def centralScalar (a : Subring.center R) : C →ₗ[R] C where
  toFun x := (a : R) • x
  map_add' := smul_add (a : R)
  map_smul' r x := by
    change (a : R) • (r • x) = r • ((a : R) • x)
    simp only [smul_smul, (Subring.mem_center_iff.mp a.property r)]

/-- Central ring scalars act as germ endomorphisms. -/
def centralMap : Subring.center R →+* End R e C where
  toFun a := Hom.ofLinearMap (centralScalar a)
  map_one' := by
    have he : centralScalar (C := C) (1 : Subring.center R) = LinearMap.id :=
      LinearMap.ext fun x => one_smul R x
    change Hom.ofLinearMap _ = Hom.id
    rw [he, Hom.ofLinearMap_id]
  map_mul' a b := by
    change Hom.ofLinearMap _ = Hom.comp (Hom.ofLinearMap _) (Hom.ofLinearMap _)
    rw [← Hom.ofLinearMap_comp]
    apply congrArg (Hom.ofLinearMap (R := R) (e := e))
    exact LinearMap.ext fun x => mul_smul (a : R) (b : R) x
  map_zero' := by
    have he : centralScalar (C := C) (0 : Subring.center R) = 0 :=
      LinearMap.ext fun x => zero_smul R x
    change Hom.ofLinearMap _ = 0
    rw [he, Hom.ofLinearMap_zero]
  map_add' a b := by
    change Hom.ofLinearMap _ = Hom.ofLinearMap _ + Hom.ofLinearMap _
    rw [← Hom.ofLinearMap_add]
    apply congrArg (Hom.ofLinearMap (R := R) (e := e))
    exact LinearMap.ext fun x => add_smul (a : R) (b : R) x

/-- Central scalar maps commute with every germ, including partial maps. -/
theorem centralMap_commute (a : Subring.center R) (f : End R e C) :
    Commute (centralMap (R := R) (e := e) (C := C) a) f := by
  have he : Hom.reducedMap (e := e)
      (centralScalar (C := C) a) =
      centralScalar (C := C ⧸ smallRadical R e C) a := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (smallRadical R e C) x
    rfl
  change PartialHom.comp (PartialHom.ofLinearMap _) f =
    PartialHom.comp f (PartialHom.ofLinearMap _)
  rw [he]
  induction f using Quotient.inductionOn with | _ f =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  have hx' := f.pullback_le _ hx
  change (a : R) • f.val.toFun _ = f.val.toFun _
  have hm := f.val.toFun.map_smul (a : R) (⟨x, hx'⟩ : f.val.domain)
  exact hm.symm

/-- The central scalar homomorphism with its central codomain recorded. -/
def centerMap : Subring.center R →+* Subring.center (End R e C) :=
  (centralMap (R := R) (e := e) (C := C)).codRestrict _ (fun a =>
    Subring.mem_center_iff.mpr fun f => (centralMap_commute a f).eq.symm)

/-- A field of central scalars embeds into the Schur ring. -/
theorem centralMap_comp_injective {K : Type*} [Field K]
    (κ : K →+* Subring.center R) [IsNoetherian R C] (hC : Critical R e C) :
    Function.Injective ((centralMap (R := R) (e := e) (C := C)).comp κ) := by
  let : DivisionRing (End R e C) := divisionRing hC
  exact RingHom.injective _

end End

section RightSection

open MulOpposite

variable (R : Type u) [Ring R] (e : ℕ)
variable (C : Type v) [AddCommGroup C] [Module Rᵐᵒᵖ C]

/-- The section module of germs from the right regular module. -/
abbrev Section := Hom Rᵐᵒᵖ e R C

namespace Section

variable {R e C}

/-- Left multiplication on the right regular module. -/
def leftMul (r : R) : R →ₗ[Rᵐᵒᵖ] R where
  toFun s := r * s
  map_add' := mul_add r
  map_smul' a s := (mul_assoc r s (unop a)).symm

@[simp] theorem leftMul_one : leftMul (1 : R) = LinearMap.id := by ext; simp [leftMul]
@[simp] theorem leftMul_zero : leftMul (0 : R) = 0 := by ext; simp [leftMul]
theorem leftMul_add (r s : R) : leftMul (r + s) = leftMul r + leftMul s := by
  ext; exact add_mul _ _ _
theorem leftMul_mul (r s : R) : leftMul (r * s) = (leftMul r).comp (leftMul s) := by
  ext; exact mul_assoc _ _ _

instance : SMul Rᵐᵒᵖ (Section R e C) :=
  ⟨fun r w => Hom.comp w (Hom.ofLinearMap (leftMul (unop r)))⟩

instance : Module Rᵐᵒᵖ (Section R e C) where
  one_smul w := by
    change Hom.comp w (Hom.ofLinearMap (leftMul 1)) = w
    rw [leftMul_one, Hom.ofLinearMap_id, Hom.comp_id]
  mul_smul r s w := by
    change Hom.comp w (Hom.ofLinearMap (leftMul (unop s * unop r))) = _
    rw [leftMul_mul, Hom.ofLinearMap_comp, ← Hom.comp_assoc]
    rfl
  smul_add r w v := Hom.add_comp _ _ _
  smul_zero r := show Hom.comp 0 _ = 0 from PartialHom.zero_comp _
  add_smul r s w := by
    change Hom.comp w (Hom.ofLinearMap (leftMul (unop r + unop s))) = _
    rw [leftMul_add, Hom.ofLinearMap_add, Hom.comp_add]
    rfl
  zero_smul w := by
    change Hom.comp w (Hom.ofLinearMap (leftMul 0)) = 0
    rw [leftMul_zero, Hom.ofLinearMap_zero]
    exact PartialHom.comp_zero w

/-- The displayed right action has the original multiplication order. -/
theorem right_action_assoc (w : Section R e C) (r s : R) :
    op s • (op r • w) = op (r * s) • w := (mul_smul (op s) (op r) w).symm

instance : SMulCommClass (End Rᵐᵒᵖ e C) Rᵐᵒᵖ (Section R e C) where
  smul_comm a r w :=
    (Hom.comp_assoc a w (Hom.ofLinearMap (leftMul (unop r)))).symm

instance : SMulCommClass Rᵐᵒᵖ (End Rᵐᵒᵖ e C) (Section R e C) :=
  SMulCommClass.symm _ _ _

/-- The total map represented by an element of a right module. -/
def elementMap (c : C) : R →ₗ[Rᵐᵒᵖ] C where
  toFun r := op r • c
  map_add' r s := add_smul (op r) (op s) c
  map_smul' r s := by
    change op (s * unop r) • c = r • (op s • c)
    exact mul_smul r (op s) c

/-- The canonical map from a module to its germ section. -/
def ofElement : C →ₗ[Rᵐᵒᵖ] Section R e C where
  toFun c := Hom.ofLinearMap (elementMap c)
  map_add' c d := by
    have he : elementMap (R := R) (c + d) = elementMap c + elementMap d := by
      apply LinearMap.ext
      intro r
      exact smul_add _ _ _
    rw [he, Hom.ofLinearMap_add]
  map_smul' r c := by
    change Hom.ofLinearMap (elementMap (r • c)) =
      Hom.comp (Hom.ofLinearMap (elementMap c)) (Hom.ofLinearMap (leftMul (unop r)))
    have he : elementMap (R := R) (r • c) =
        (elementMap c).comp (leftMul (unop r)) := by
      apply LinearMap.ext
      intro s
      exact (mul_smul (op s) r c).symm
    rw [he, Hom.ofLinearMap_comp]

/-- Critical modules embed into their section modules. -/
theorem ofElement_injective [IsNoetherian Rᵐᵒᵖ C] (hC : Critical Rᵐᵒᵖ e C) :
    Function.Injective (ofElement (R := R) (e := e) (C := C)) := by
  have hzero : ∀ c : C, ofElement (R := R) (e := e) c = 0 → c = 0 := by
    intro c hc
    have hs := (Hom.ofLinearMap_eq_zero_iff (elementMap (R := R) c)).mp hc
    have hr : (elementMap (R := R) c).range = ⊥ := by
      by_contra hr
      exact hC.not_small_submodule hr hs
    have hm : c ∈ (elementMap (R := R) c).range := ⟨1, by simp [elementMap]⟩
    exact hr.le hm
  intro c d he
  exact sub_eq_zero.mp (hzero (c - d) (by rw [map_sub, he, sub_self]))

/-- Clearing one element of a representative's domain turns its germ into
a total element map. This identity fixes the right-action orientation. -/
theorem smul_mk_eq_ofElement [IsNoetherian Rᵐᵒᵖ C]
    (hC : Critical Rᵐᵒᵖ e C)
    (f : Representative Rᵐᵒᵖ e (R ⧸ smallRadical Rᵐᵒᵖ e R)
      (C ⧸ smallRadical Rᵐᵒᵖ e C))
    (i : R) (hi : (smallRadical Rᵐᵒᵖ e R).mkQ i ∈ f.val.domain) :
    op i • (PartialHom.mk f : Section R e C) =
      ofElement ((smallRadical Rᵐᵒᵖ e C).quotEquivOfEqBot hC.smallRadical_eq_bot
        (f.val ⟨(smallRadical Rᵐᵒᵖ e R).mkQ i, hi⟩)) := by
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective (smallRadical Rᵐᵒᵖ e R) x
  change f.val.toFun _ = (smallRadical Rᵐᵒᵖ e C).mkQ _
  have he : (Hom.reducedMap (e := e) (leftMul i))
      ((smallRadical Rᵐᵒᵖ e R).mkQ s) =
      op s • (smallRadical Rᵐᵒᵖ e R).mkQ i := by
    change (smallRadical Rᵐᵒᵖ e R).mkQ (i * s) = _
    exact ((smallRadical Rᵐᵒᵖ e R).mkQ.map_smul (op s) i).symm
  have he' : (⟨(Hom.reducedMap (e := e) (leftMul i))
      ((smallRadical Rᵐᵒᵖ e R).mkQ s),
      (Representative.mem_pullback
        (Representative.ofLinearMap (Hom.reducedMap (e := e) (leftMul i)))
        f.val.domain Submodule.mem_top).mp hx⟩ : f.val.domain) =
      op s • (⟨(smallRadical Rᵐᵒᵖ e R).mkQ i, hi⟩ : f.val.domain) :=
    Subtype.ext he
  change f.val.toFun (⟨_, _⟩ : f.val.domain) = _
  calc
    _ = f.val.toFun (op s • (⟨(smallRadical Rᵐᵒᵖ e R).mkQ i, hi⟩ : f.val.domain)) :=
      congrArg f.val.toFun he'
    _ = op s • f.val.toFun ⟨(smallRadical Rᵐᵒᵖ e R).mkQ i, hi⟩ := map_smul _ _ _
    _ = _ := by
      change _ = (smallRadical Rᵐᵒᵖ e C).mkQ (op s • _)
      rw [map_smul]
      congr 1
      exact (((smallRadical Rᵐᵒᵖ e C).quotEquivOfEqBot
        hC.smallRadical_eq_bot).symm_apply_apply _).symm

/-- Every nonzero section vector has a nonzero right multiple in the
embedded critical module. No Ore or domain hypothesis is needed here. -/
theorem exists_smul_eq_ofElement [IsNoetherian Rᵐᵒᵖ C]
    (hC : Critical Rᵐᵒᵖ e C) (w : Section R e C) (hw : w ≠ 0) :
    ∃ i : R, ∃ c : C, c ≠ 0 ∧ op i • w = ofElement c := by
  induction w using Quotient.inductionOn with | _ f =>
  have hf : f.val.toFun ≠ 0 := fun hz => hw
    ((PartialHom.mk_eq_zero_iff_of_critical (critical_quotient_smallRadical hC) f).mpr hz)
  have hex : ∃ x : f.val.domain, f.val.toFun x ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hf (LinearMap.ext hn)
  obtain ⟨x, hx⟩ := hex
  obtain ⟨i, hi⟩ := Submodule.mkQ_surjective (smallRadical Rᵐᵒᵖ e R) x.val
  let a := (smallRadical Rᵐᵒᵖ e C).quotEquivOfEqBot hC.smallRadical_eq_bot
  refine ⟨i, a (f.val.toFun x), fun hz => hx (a.injective (hz.trans a.map_zero.symm)), ?_⟩
  have hm : (smallRadical Rᵐᵒᵖ e R).mkQ i ∈ f.val.domain := hi ▸ x.property
  have he := smul_mk_eq_ofElement hC f i hm
  exact he.trans (congrArg (fun z : f.val.domain => ofElement (a (f.val.toFun z)))
    (Subtype.ext hi))

/-- The canonical copy of a critical module is essential in its section:
every nonzero submodule has a nonzero inverse image in that copy. -/
theorem comap_ofElement_ne_bot [IsNoetherian Rᵐᵒᵖ C]
    (hC : Critical Rᵐᵒᵖ e C) {U : Submodule Rᵐᵒᵖ (Section R e C)} (hU : U ≠ ⊥) :
    U.comap ofElement ≠ ⊥ := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨i, c, hc, he⟩ := exists_smul_eq_ofElement hC w hw0
  intro hz
  have hm : c ∈ U.comap ofElement := by
    change ofElement c ∈ U
    rw [← he]
    exact U.smul_mem (op i) hw
  exact hc (hz.le hm)

/-- Section modules of critical modules are uniform. -/
theorem inf_ne_bot [IsNoetherian Rᵐᵒᵖ C] (hC : Critical Rᵐᵒᵖ e C)
    {U V : Submodule Rᵐᵒᵖ (Section R e C)} (hU : U ≠ ⊥) (hV : V ≠ ⊥) :
    U ⊓ V ≠ ⊥ := by
  have hn := hC.inf_ne_bot (comap_ofElement_ne_bot hC hU) (comap_ofElement_ne_bot hC hV)
  intro he
  apply hn
  rw [← Submodule.comap_inf, he, Submodule.comap_bot]
  exact (LinearMap.ker_eq_bot).mpr (ofElement_injective hC)

/-- No nonzero submodule of a critical section is locally small. -/
theorem eq_bot_of_locSmall [IsNoetherian Rᵐᵒᵖ C] (hC : Critical Rᵐᵒᵖ e C)
    (U : Submodule Rᵐᵒᵖ (Section R e C)) (hU : LocSmall Rᵐᵒᵖ e U) : U = ⊥ := by
  by_contra hn
  let V := U.comap ofElement
  let f : V →ₗ[Rᵐᵒᵖ] U :=
    (ofElement.comp V.subtype).codRestrict U (fun x => x.property)
  have hi : Function.Injective f := by
    intro x y he
    exact Subtype.ext (ofElement_injective hC (congrArg Subtype.val he))
  exact hC.not_small_submodule (comap_ofElement_ne_bot hC hn)
    (locSmall_iff_small.mp (hU.of_injective f hi))

/-- Over a domain, ordinary elementwise torsion passes from a critical
module to its section. The scalar product used is literally `i * s`. -/
theorem torsion [NoZeroDivisors R] [IsNoetherian Rᵐᵒᵖ C]
    (hC : Critical Rᵐᵒᵖ e C)
    (ht : ∀ c : C, ∃ s : R, s ≠ 0 ∧ op s • c = 0) :
    ∀ w : Section R e C, ∃ s : R, s ≠ 0 ∧ op s • w = 0 := by
  intro w
  by_cases hw : w = 0
  · obtain ⟨s, hs, _⟩ := ht 0
    exact ⟨s, hs, by rw [hw, smul_zero]⟩
  obtain ⟨i, c, hc, he⟩ := exists_smul_eq_ofElement hC w hw
  have hi : i ≠ 0 := by
    intro hi
    rw [hi, op_zero, zero_smul] at he
    exact hc (ofElement_injective hC (he.symm.trans (map_zero ofElement).symm))
  obtain ⟨s, hs, hsc⟩ := ht c
  refine ⟨i * s, mul_ne_zero hi hs, ?_⟩
  rw [← right_action_assoc, he, ← map_smul, hsc, map_zero]

end Section
end RightSection

end Germ
end Module
