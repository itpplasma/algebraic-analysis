module
public import AlgebraicAnalysis.Module.LocSmall
public import Mathlib.LinearAlgebra.LinearPMap

@[expose] public section

/-!
# Dense partial linear maps and germs

The partial-map calculus is category-free. Equality is witnessed on a common
dense submodule. Quotienting the target by the small radical gives normalized
germs for Noetherian modules; right modules use opposite scalars throughout.
The pair correspondence below requires Noetherian source and target; no
quotient-valued correspondence for arbitrary modules is asserted.
-/

universe u v w z

namespace Module
namespace Germ

variable (R : Type u) [Ring R] (e : ℕ)
variable (M : Type v) (N : Type w) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A partial linear map with small domain quotient. -/
def Representative := {f : M →ₗ.[R] N // Dense R e f.domain}

variable {R e M N}
variable {P : Type z} [AddCommGroup P] [Module R P]

namespace Representative

/-- Agreement after a common dense restriction. -/
def Rel (f g : Representative R e M N) : Prop :=
  ∃ U : Submodule R M, Dense R e U ∧ ∃ hf : U ≤ f.val.domain,
    ∃ hg : U ≤ g.val.domain,
      ∀ x : U, f.val ⟨x, hf x.property⟩ = g.val ⟨x, hg x.property⟩

theorem Rel.refl (f : Representative R e M N) : Rel f f :=
  ⟨f.val.domain, f.property, le_rfl, le_rfl, fun _ => rfl⟩

theorem Rel.symm {f g : Representative R e M N} (h : Rel f g) : Rel g f := by
  obtain ⟨U, hU, hf, hg, h⟩ := h
  exact ⟨U, hU, hg, hf, fun x => (h x).symm⟩

theorem Rel.trans {f g h : Representative R e M N} (hfg : Rel f g) (hgh : Rel g h) :
    Rel f h := by
  obtain ⟨U, hU, hf, hg, huv⟩ := hfg
  obtain ⟨V, hV, hg', hh, hvw⟩ := hgh
  exact ⟨U ⊓ V, hU.inf hV, inf_le_left.trans hf, inf_le_right.trans hh,
    fun x => (huv ⟨x, x.property.1⟩).trans (hvw ⟨x, x.property.2⟩)⟩

instance setoid : Setoid (Representative R e M N) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

instance : Zero (Representative R e M N) := ⟨⟨0, dense_top⟩⟩
instance : Add (Representative R e M N) :=
  ⟨fun f g => ⟨f.val + g.val, f.property.inf g.property⟩⟩
instance : Neg (Representative R e M N) := ⟨fun f => ⟨-f.val, f.property⟩⟩

@[simp] theorem zero_val : (0 : Representative R e M N).val = 0 := rfl
@[simp] theorem add_val (f g : Representative R e M N) : (f + g).val = f.val + g.val := rfl
@[simp] theorem neg_val (f : Representative R e M N) : (-f).val = -f.val := rfl

theorem Rel.add {f f' g g' : Representative R e M N} (hf : Rel f f') (hg : Rel g g') :
    Rel (f + g) (f' + g') := by
  obtain ⟨U, hU, hUf, hUf', hff'⟩ := hf
  obtain ⟨V, hV, hVg, hVg', hgg'⟩ := hg
  refine ⟨U ⊓ V, hU.inf hV,
    le_inf (inf_le_left.trans hUf) (inf_le_right.trans hVg),
    le_inf (inf_le_left.trans hUf') (inf_le_right.trans hVg'), ?_⟩
  intro x
  exact congrArg₂ (· + ·) (hff' ⟨x, x.property.1⟩) (hgg' ⟨x, x.property.2⟩)

theorem Rel.neg {f g : Representative R e M N} (h : Rel f g) : Rel (-f) (-g) := by
  obtain ⟨U, hU, hf, hg, h⟩ := h
  exact ⟨U, hU, hf, hg, fun x => congrArg Neg.neg (h x)⟩

/-- Pull back a submodule through a partial map, inside the ambient source. -/
def pullback (f : Representative R e M N) (U : Submodule R N) : Submodule R M :=
  (U.comap f.val.toFun).map f.val.domain.subtype

theorem pullback_le (f : Representative R e M N) (U : Submodule R N) :
    f.pullback U ≤ f.val.domain := Submodule.map_subtype_le _ _

theorem mem_pullback (f : Representative R e M N) (U : Submodule R N)
    {x : M} (hx : x ∈ f.val.domain) :
    x ∈ f.pullback U ↔ f.val ⟨x, hx⟩ ∈ U := by
  constructor
  · rintro ⟨y, hy, he⟩
    have he' : y = (⟨x, hx⟩ : f.val.domain) := Subtype.ext he
    change f.val.toFun y ∈ U at hy
    simpa only [he', LinearPMap.toFun_eq_coe] using hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem dense_pullback (f : Representative R e M N) {U : Submodule R N}
    (hU : Dense R e U) : Dense R e (f.pullback U) :=
  f.property.map_subtype (hU.comap f.val.toFun)

/-- Composition uses the inverse image of the second domain. -/
def comp (g : Representative R e N P) (f : Representative R e M N) :
    Representative R e M P :=
  let D := f.pullback g.val.domain
  let a : D →ₗ[R] N := f.val.toFun.comp (Submodule.inclusion (f.pullback_le _))
  let b : D →ₗ[R] g.val.domain := a.codRestrict _
    (fun x => (f.mem_pullback _ _).mp x.property)
  ⟨⟨D, g.val.toFun.comp b⟩, f.dense_pullback g.property⟩

theorem comp_apply (g : Representative R e N P) (f : Representative R e M N)
    (x : M) (hx : x ∈ f.val.domain) (hy : f.val ⟨x, hx⟩ ∈ g.val.domain) :
    (g.comp f).val ⟨x, (f.mem_pullback _ hx).mpr hy⟩ = g.val ⟨f.val ⟨x, hx⟩, hy⟩ := rfl

theorem Rel.comp {g g' : Representative R e N P} {f f' : Representative R e M N}
    (hg : Rel g g') (hf : Rel f f') : Rel (g.comp f) (g'.comp f') := by
  obtain ⟨U, hU, hUf, hUf', hff'⟩ := hf
  obtain ⟨V, hV, hVg, hVg', hgg'⟩ := hg
  let W := U ⊓ f.pullback V
  have hwf (x : W) : f.val ⟨x, hUf x.property.1⟩ ∈ V :=
    (f.mem_pullback V _).mp x.property.2
  have hwf' (x : W) : f'.val ⟨x, hUf' x.property.1⟩ ∈ V := by
    rw [← hff' ⟨x, x.property.1⟩]; exact hwf x
  refine ⟨W, hU.inf (f.dense_pullback hV), ?_, ?_, ?_⟩
  · intro x hx
    exact (f.mem_pullback _ (hUf hx.1)).mpr (hVg (hwf ⟨x, hx⟩))
  · intro x hx
    exact (f'.mem_pullback _ (hUf' hx.1)).mpr (hVg' (hwf' ⟨x, hx⟩))
  · intro x
    change g.val _ = g'.val _
    have h := hgg' ⟨f.val ⟨x, hUf x.property.1⟩, hwf x⟩
    refine h.trans ?_
    congr 1
    exact Subtype.ext (hff' ⟨x, x.property.1⟩)

/-- Total maps are representatives on the top submodule. -/
def ofLinearMap (f : M →ₗ[R] N) : Representative R e M N := ⟨f.toPMap ⊤, dense_top⟩

/-- Agreement throughout the common domain gives a germ equality. -/
theorem rel_of_eq (f g : Representative R e M N)
    (h : ∀ x (hf : x ∈ f.val.domain) (hg : x ∈ g.val.domain),
      f.val ⟨x, hf⟩ = g.val ⟨x, hg⟩) : Rel f g :=
  ⟨f.val.domain ⊓ g.val.domain, f.property.inf g.property, inf_le_left, inf_le_right,
    fun x => h x x.property.1 x.property.2⟩

/-- Restricting a dense-range map to a dense submodule keeps its range dense. -/
theorem dense_range_restrict (f : Representative R e M N) (U : Submodule R M)
    (hU : Dense R e U) (hUf : U ≤ f.val.domain)
    (hf : Dense R e f.val.toFun.range) :
    Dense R e (f.val.toFun.comp (Submodule.inclusion hUf)).range := by
  have h := hf.map_subtype ((hU.comap f.val.domain.subtype).map
    f.val.toFun.rangeRestrict (by rintro ⟨y, x, rfl⟩; exact ⟨x, rfl⟩))
  have he : (((U.comap f.val.domain.subtype).map f.val.toFun.rangeRestrict).map
      f.val.toFun.range.subtype) = (f.val.toFun.comp (Submodule.inclusion hUf)).range := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x.val, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨f.val.toFun.rangeRestrict ⟨x, hUf x.property⟩,
        ⟨⟨x, hUf x.property⟩, x.property, rfl⟩, rfl⟩
  rwa [he] at h

/-- Dense range is independent of the representative. -/
theorem Rel.dense_range_iff {f g : Representative R e M N} (h : Rel f g) :
    Dense R e f.val.toFun.range ↔ Dense R e g.val.toFun.range := by
  suffices ∀ (f g : Representative R e M N), Rel f g →
      Dense R e f.val.toFun.range → Dense R e g.val.toFun.range from
    ⟨this f g h, this g f h.symm⟩
  intro f g h hf
  obtain ⟨U, hU, hUf, hUg, he⟩ := h
  have hmap : f.val.toFun.comp (Submodule.inclusion hUf) =
      g.val.toFun.comp (Submodule.inclusion hUg) := by ext x; exact he x
  have hd := f.dense_range_restrict U hU hUf hf
  rw [hmap] at hd
  exact hd.mono (LinearMap.range_comp_le_range _ _)

end Representative

/-- Germs of dense partial maps with a fixed (unquotiented) target.
`Hom` below uses radical quotients for both objects. -/
def PartialHom (R : Type u) [Ring R] (e : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :=
  Quotient (Representative.setoid (R := R) (e := e) (M := M) (N := N))

namespace PartialHom

/-- Take the equivalence class of a dense partial map. -/
def mk (f : Representative R e M N) : PartialHom R e M N := Quotient.mk' f

theorem mk_eq_mk {f g : Representative R e M N} : mk f = mk g ↔ Representative.Rel f g :=
  Quotient.eq

instance : Zero (PartialHom R e M N) := ⟨mk 0⟩
instance : Add (PartialHom R e M N) :=
  ⟨Quotient.map₂ (· + ·) (fun _ _ hf _ _ hg => Representative.Rel.add hf hg)⟩
instance : Neg (PartialHom R e M N) := ⟨Quotient.map Neg.neg (fun _ _ h => h.neg)⟩

@[simp] theorem mk_zero : mk (0 : Representative R e M N) = 0 := rfl
@[simp] theorem mk_add (f g : Representative R e M N) : mk (f + g) = mk f + mk g := rfl
@[simp] theorem mk_neg (f : Representative R e M N) : mk (-f) = -mk f := rfl

/-- Composition on equivalence classes. -/
def comp (g : PartialHom R e N P) (f : PartialHom R e M N) : PartialHom R e M P :=
  Quotient.map₂ Representative.comp
    (fun _ _ hg _ _ hf => Representative.Rel.comp hg hf) g f

@[simp] theorem mk_comp (g : Representative R e N P) (f : Representative R e M N) :
    mk (g.comp f) = (mk g).comp (mk f) := rfl

/-- The germ of a total linear map. -/
def ofLinearMap (f : M →ₗ[R] N) : PartialHom R e M N := mk (.ofLinearMap f)

theorem add_assoc (f g h : PartialHom R e M N) : (f + g) + h = f + (g + h) := by
  induction f using Quotient.inductionOn with | _ f =>
  induction g using Quotient.inductionOn with | _ g =>
  induction h using Quotient.inductionOn with | _ h =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  change (f.val _ + g.val _) + h.val _ = f.val _ + (g.val _ + h.val _)
  exact _root_.add_assoc _ _ _

theorem add_comm (f g : PartialHom R e M N) : f + g = g + f := by
  induction f using Quotient.inductionOn with | _ f =>
  induction g using Quotient.inductionOn with | _ g =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  change f.val _ + g.val _ = g.val _ + f.val _
  exact _root_.add_comm _ _

theorem zero_add (f : PartialHom R e M N) : 0 + f = f := by
  induction f using Quotient.inductionOn with | _ f =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  change 0 + f.val _ = f.val _
  exact _root_.zero_add _

theorem add_zero (f : PartialHom R e M N) : f + 0 = f := by rw [add_comm, zero_add]

theorem neg_add_cancel (f : PartialHom R e M N) : -f + f = 0 := by
  induction f using Quotient.inductionOn with | _ f =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  change -f.val _ + f.val _ = 0
  exact _root_.neg_add_cancel _

instance : AddCommGroup (PartialHom R e M N) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  neg_add_cancel := neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

variable {Q : Type*} [AddCommGroup Q] [Module R Q]

/-- Associativity of composition is proved on partial-map representatives. -/
theorem comp_assoc (h : PartialHom R e P Q) (g : PartialHom R e N P)
    (f : PartialHom R e M N) : (h.comp g).comp f = h.comp (g.comp f) := by
  induction h using Quotient.inductionOn with | _ h =>
  induction g using Quotient.inductionOn with | _ g =>
  induction f using Quotient.inductionOn with | _ f =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  rfl

theorem add_comp (g h : PartialHom R e N P) (f : PartialHom R e M N) :
    (g + h).comp f = g.comp f + h.comp f := by
  induction g using Quotient.inductionOn with | _ g =>
  induction h using Quotient.inductionOn with | _ h =>
  induction f using Quotient.inductionOn with | _ f =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  rfl

/-- Right distributivity needs a smaller domain on which both summands are defined. -/
theorem comp_add (h : PartialHom R e N P) (f g : PartialHom R e M N) :
    h.comp (f + g) = h.comp f + h.comp g := by
  induction h using Quotient.inductionOn with | _ h =>
  induction f using Quotient.inductionOn with | _ f =>
  induction g using Quotient.inductionOn with | _ g =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  change h.val.toFun _ = h.val.toFun _ + h.val.toFun _
  rw [← map_add]
  congr 1

@[simp] theorem id_comp (f : PartialHom R e M N) : (ofLinearMap LinearMap.id).comp f = f := by
  induction f using Quotient.inductionOn with | _ f =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intros; rfl

@[simp] theorem comp_id (f : PartialHom R e M N) : f.comp (ofLinearMap LinearMap.id) = f := by
  induction f using Quotient.inductionOn with | _ f =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intros; rfl

/-- A total map vanishes precisely when its image belongs to the small stratum. -/
theorem ofLinearMap_eq_zero_iff (f : M →ₗ[R] N) :
    ofLinearMap (e := e) f = 0 ↔ Small R e (LinearMap.range f) := by
  constructor
  · intro h
    obtain ⟨U, hU, hf, hg, he⟩ := Quotient.exact h
    have hu : U ≤ LinearMap.ker f := by
      intro x hx
      exact he ⟨x, hx⟩
    exact (small_linearEquiv_iff e f.quotKerEquivRange).mp (hU.mono hu)
  · intro h
    apply Quotient.sound
    refine ⟨LinearMap.ker f, ?_, le_top, le_top, ?_⟩
    · exact (small_linearEquiv_iff e f.quotKerEquivRange).mpr h
    · intro x
      exact x.property

/-- Epicity modulo small modules is the explicit cokernel condition. -/
def EpicMod (f : M →ₗ[R] N) : Prop := Small R e (N ⧸ LinearMap.range f)

@[simp] theorem epicMod_iff (f : M →ₗ[R] N) :
    EpicMod (e := e) f ↔ Small R e (N ⧸ LinearMap.range f) := Iff.rfl

/-- A germ is epic modulo small modules when a representative has dense range. -/
def Epic (f : PartialHom R e M N) : Prop :=
  Quotient.lift (fun f : Representative R e M N => Dense R e f.val.toFun.range)
    (fun _ _ h => propext (Representative.Rel.dense_range_iff h)) f

@[simp] theorem epic_mk (f : Representative R e M N) :
    Epic (mk f) ↔ Dense R e f.val.toFun.range := Iff.rfl

/-- Epicity of a total germ is exactly the small-cokernel condition. -/
theorem epic_ofLinearMap_iff (f : M →ₗ[R] N) :
    Epic (ofLinearMap (e := e) f) ↔ Small R e (N ⧸ LinearMap.range f) := by
  change Dense R e ((f.comp (⊤ : Submodule R M).subtype).range) ↔ _
  have he : (f.comp (⊤ : Submodule R M).subtype).range = f.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.val, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩
  rw [he]
  rfl

@[simp] theorem ofLinearMap_zero : ofLinearMap (e := e) (0 : M →ₗ[R] N) = 0 := rfl

theorem ofLinearMap_add (f g : M →ₗ[R] N) :
    ofLinearMap (e := e) (f + g) = ofLinearMap f + ofLinearMap g := by
  apply Quotient.sound
  apply Representative.rel_of_eq
  intros; rfl

theorem ofLinearMap_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    ofLinearMap (e := e) (g.comp f) = (ofLinearMap g).comp (ofLinearMap f) := by
  apply Quotient.sound
  apply Representative.rel_of_eq
  intros; rfl

@[simp] theorem zero_comp (f : PartialHom R e M N) : (0 : PartialHom R e N P).comp f = 0 := by
  induction f using Quotient.inductionOn with | _ f =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intros; rfl

@[simp] theorem comp_zero (g : PartialHom R e N P) : g.comp (0 : PartialHom R e M N) = 0 := by
  induction g using Quotient.inductionOn with | _ g =>
  apply Quotient.sound
  apply Representative.rel_of_eq
  intros
  exact g.val.toFun.map_zero

/-- Dense range gives the categorical right-cancellation property. -/
theorem Epic.right_cancel {f : PartialHom R e M N} (hf : Epic f)
    (g h : PartialHom R e N P) (he : g.comp f = h.comp f) : g = h := by
  induction f using Quotient.inductionOn with | _ f =>
  induction g using Quotient.inductionOn with | _ g =>
  induction h using Quotient.inductionOn with | _ h =>
  obtain ⟨U, hU, hUg, hUh, hgh⟩ := Quotient.exact he
  have hUf : U ≤ f.val.domain := hUg.trans (f.pullback_le _)
  let a := f.val.toFun.comp (Submodule.inclusion hUf)
  have hag : a.range ≤ g.val.domain := by
    rintro y ⟨x, rfl⟩
    exact (f.mem_pullback _ _).mp (hUg x.property)
  have hah : a.range ≤ h.val.domain := by
    rintro y ⟨x, rfl⟩
    exact (f.mem_pullback _ _).mp (hUh x.property)
  apply Quotient.sound
  refine ⟨a.range, f.dense_range_restrict U hU hUf hf, hag, hah, ?_⟩
  rintro ⟨_, x, rfl⟩
  exact hgh x

/-- Conversely a germ that cancels all following maps has dense range. -/
theorem epic_iff_right_cancel (f : PartialHom R e M N) : Epic f ↔
    ∀ (P : Type w) [AddCommGroup P] [Module R P],
      ∀ g h : PartialHom R e N P, g.comp f = h.comp f → g = h := by
  refine ⟨fun h _ _ _ g k he => h.right_cancel g k he, ?_⟩
  induction f using Quotient.inductionOn with | _ f =>
  intro hc
  let q := f.val.toFun.range.mkQ
  have he : (ofLinearMap (e := e) q).comp (mk f) = (0 : PartialHom R e N _).comp (mk f) := by
    rw [zero_comp]
    apply Quotient.sound
    apply Representative.rel_of_eq
    intro x hx hy
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  have hz := hc _ (ofLinearMap q) 0 he
  have hs := (ofLinearMap_eq_zero_iff q).mp hz
  exact hs.of_surjective q.range.subtype (by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨⟨q x, ⟨x, rfl⟩⟩, rfl⟩)

end PartialHom

/-- Normalized germ Hom. On Noetherian objects the radical is small and the
quotients have no nonzero small submodule. -/
abbrev Hom (R : Type u) [Ring R] (e : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :=
  PartialHom R e (M ⧸ smallRadical R e M) (N ⧸ smallRadical R e N)

namespace Hom

/-- The total linear map on radical quotients. -/
def reducedMap (f : M →ₗ[R] N) :
    (M ⧸ smallRadical R e M) →ₗ[R] (N ⧸ smallRadical R e N) :=
  Submodule.mapQ _ _ f (smallRadical_le_comap f)

/-- A total map determines a normalized germ. -/
def ofLinearMap (f : M →ₗ[R] N) : Hom R e M N :=
  PartialHom.ofLinearMap (reducedMap (e := e) f)

/-- Vanishing of a total map detects its actual small image. -/
theorem ofLinearMap_eq_zero_iff [IsNoetherian R N] (f : M →ₗ[R] N) :
    ofLinearMap (e := e) f = 0 ↔ Small R e (LinearMap.range f) := by
  rw [ofLinearMap, PartialHom.ofLinearMap_eq_zero_iff]
  constructor
  · intro h
    have hz : LinearMap.range (reducedMap (e := e) f) = ⊥ :=
      eq_bot_of_small_quotient_radical _ h
    apply (small_smallRadical (R := R) (e := e) (M := N)).of_le
    rintro y ⟨x, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have hx := LinearMap.mem_range_self (reducedMap (e := e) f)
      ((smallRadical R e M).mkQ x)
    rw [hz] at hx
    exact hx
  · intro h
    have hf : reducedMap (e := e) f = 0 := by
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (smallRadical R e M) x
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (le_smallRadical h (LinearMap.mem_range_self f x))
    rw [hf, LinearMap.range_zero]
    exact small_of_subsingleton e

/-- The epic germ condition on normalized objects. -/
abbrev Epic (f : Hom R e M N) : Prop := PartialHom.Epic f

/-- On Noetherian targets normalization preserves the exact cokernel criterion. -/
theorem epic_ofLinearMap_iff [IsNoetherian R N] (f : M →ₗ[R] N) :
    Epic (ofLinearMap (e := e) f) ↔ Small R e (N ⧸ LinearMap.range f) := by
  change PartialHom.Epic (PartialHom.ofLinearMap (reducedMap (e := e) f)) ↔ _
  rw [PartialHom.epic_ofLinearMap_iff]
  change Dense R e (reducedMap (e := e) f).range ↔ Dense R e f.range
  rw [reducedMap, Submodule.range_mapQ]
  constructor
  · intro h
    have hd := h.comap (smallRadical R e N).mkQ
    rw [Submodule.comap_map_mkQ] at hd
    exact hd.of_small_sup small_smallRadical
  · intro h
    exact h.map _ (Submodule.mkQ_surjective _)

/-- Composition of normalized germs. -/
abbrev comp (g : Hom R e N P) (f : Hom R e M N) : Hom R e M P := PartialHom.comp g f

/-- The identity germ. -/
def id : Hom R e M M := PartialHom.ofLinearMap LinearMap.id

variable {Q : Type*} [AddCommGroup Q] [Module R Q]

theorem comp_assoc (h : Hom R e P Q) (g : Hom R e N P) (f : Hom R e M N) :
    comp (comp h g) f = comp h (comp g f) := PartialHom.comp_assoc h g f

theorem add_comp (g h : Hom R e N P) (f : Hom R e M N) :
    comp (g + h) f = comp g f + comp h f := PartialHom.add_comp g h f

theorem comp_add (h : Hom R e N P) (f g : Hom R e M N) :
    comp h (f + g) = comp h f + comp h g := PartialHom.comp_add h f g

@[simp] theorem id_comp (f : Hom R e M N) : comp id f = f := PartialHom.id_comp f
@[simp] theorem comp_id (f : Hom R e M N) : comp f id = f := PartialHom.comp_id f

@[simp] theorem ofLinearMap_id : ofLinearMap (e := e) (LinearMap.id : M →ₗ[R] M) = id := by
  unfold ofLinearMap reducedMap id
  rw [Submodule.mapQ_id]

theorem ofLinearMap_add (f g : M →ₗ[R] N) :
    ofLinearMap (e := e) (f + g) = ofLinearMap f + ofLinearMap g := by
  have hm : reducedMap (e := e) (f + g) = reducedMap f + reducedMap g := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (smallRadical R e M) x
    rfl
  unfold ofLinearMap
  rw [hm, PartialHom.ofLinearMap_add]

theorem ofLinearMap_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    ofLinearMap (e := e) (g.comp f) = comp (ofLinearMap g) (ofLinearMap f) := by
  have hm : reducedMap (e := e) (g.comp f) = (reducedMap g).comp (reducedMap f) := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (smallRadical R e M) x
    rfl
  unfold ofLinearMap
  rw [hm, PartialHom.ofLinearMap_comp]

/-- An epic normalized germ cancels following normalized germs. -/
theorem Epic.right_cancel {f : Hom R e M N} (hf : Epic f) (g h : Hom R e N P)
    (he : comp g f = comp h f) : g = h := PartialHom.Epic.right_cancel hf g h he

end Hom

/-- A quotient-valued representative in the original modules. -/
structure Pair (R : Type u) [Ring R] (e : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] where
  /-- Dense domain in the source. -/
  domain : Submodule R M
  dense_domain : Dense R e domain
  /-- Small target denominator. -/
  target : Submodule R N
  small_target : Small R e target
  /-- The partial quotient-valued map. -/
  map : domain →ₗ[R] (N ⧸ target)

namespace Pair

variable (p : Pair R e M N)

/-- Enlarge the target denominator to the small radical. -/
def targetMap : p.domain →ₗ[R] (N ⧸ smallRadical R e N) :=
  (Submodule.mapQ p.target (smallRadical R e N) LinearMap.id
    (le_smallRadical p.small_target)).comp p.map

/-- The image of the original domain in the reduced source. -/
def domainMap : p.domain →ₗ[R] p.domain.map (smallRadical R e M).mkQ :=
  (smallRadical R e M).mkQ.submoduleMap p.domain

theorem domainMap_surjective : Function.Surjective p.domainMap := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem ker_domainMap_le [IsNoetherian R M] [IsNoetherian R N] :
    LinearMap.ker p.domainMap ≤ LinearMap.ker p.targetMap := by
  have hk : Small R e (LinearMap.ker p.domainMap) :=
    (small_smallRadical (R := R) (e := e) (M := M)).of_injective
      { toFun := fun x => ⟨x.val.val, (Submodule.Quotient.mk_eq_zero _).mp
          (show (smallRadical R e M).mkQ x.val.val = 0 from
            congrArg Subtype.val (show p.domainMap x.val = 0 from x.property))⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      (by intro x y h; apply Subtype.ext; apply Subtype.ext
          have hh := congrArg Subtype.val h; exact hh)
  have hz := eq_bot_of_small_quotient_radical
    ((LinearMap.ker p.domainMap).map p.targetMap) (hk.map p.targetMap)
  intro x hx
  have hh : p.targetMap x ∈ (LinearMap.ker p.domainMap).map p.targetMap :=
    Submodule.mem_map_of_mem hx
  rw [hz] at hh
  exact hh

/-- Normalize both objects without choosing lifts of the quotient-valued map. -/
noncomputable def normalize [IsNoetherian R M] [IsNoetherian R N] :
    Representative R e (M ⧸ smallRadical R e M) (N ⧸ smallRadical R e N) :=
  ⟨⟨p.domain.map (smallRadical R e M).mkQ,
      ((LinearMap.ker p.domainMap).liftQ p.targetMap p.ker_domainMap_le).comp
        (p.domainMap.quotKerEquivOfSurjective p.domainMap_surjective).symm.toLinearMap⟩,
    p.dense_domain.map _ (Submodule.mkQ_surjective _)⟩

@[simp] theorem normalize_apply [IsNoetherian R M] [IsNoetherian R N] (x : p.domain) :
    p.normalize.val (p.domainMap x) = p.targetMap x := by
  change ((LinearMap.ker p.domainMap).liftQ p.targetMap p.ker_domainMap_le)
    ((p.domainMap.quotKerEquivOfSurjective p.domainMap_surjective).symm (p.domainMap x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- The normalized germ of a quotient-valued partial map. -/
noncomputable def toHom [IsNoetherian R M] [IsNoetherian R N] : Hom R e M N :=
  PartialHom.mk p.normalize

/-- The original pair attached to a total linear map uses zero target denominator. -/
def ofLinearMap (f : M →ₗ[R] N) : Pair R e M N :=
  ⟨⊤, dense_top, ⊥, small_of_subsingleton e,
    ((⊥ : Submodule R N).mkQ.comp f).comp (⊤ : Submodule R M).subtype⟩

/-- The two constructions of the germ of a total map agree. -/
theorem toHom_ofLinearMap [IsNoetherian R M] [IsNoetherian R N] (f : M →ₗ[R] N) :
    (ofLinearMap (e := e) f).toHom = Hom.ofLinearMap f := by
  apply Quotient.sound
  apply Representative.rel_of_eq
  intro x hx hy
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (smallRadical R e M) x
  change (ofLinearMap (e := e) f).normalize.val
    ((ofLinearMap (e := e) f).domainMap ⟨y, Submodule.mem_top⟩) = _
  rw [normalize_apply]
  rfl

/-- Original representatives agree after a dense restriction and a small
common enlargement of their target denominators. -/
def Rel (p q : Pair R e M N) : Prop :=
  ∃ U : Submodule R M, Dense R e U ∧ ∃ hp : U ≤ p.domain, ∃ hq : U ≤ q.domain,
    ∃ T : Submodule R N, Small R e T ∧ ∃ hpT : p.target ≤ T, ∃ hqT : q.target ≤ T,
      ∀ x : U, Submodule.mapQ p.target T LinearMap.id hpT (p.map ⟨x, hp x.property⟩) =
        Submodule.mapQ q.target T LinearMap.id hqT (q.map ⟨x, hq x.property⟩)

private theorem enlarge_trans (A B C : Submodule R N) (hAB : A ≤ B) (hBC : B ≤ C)
    (x : N ⧸ A) : Submodule.mapQ B C LinearMap.id hBC
      (Submodule.mapQ A B LinearMap.id hAB x) =
      Submodule.mapQ A C LinearMap.id (hAB.trans hBC) x := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective A x
  rfl

/-- Normalization has exactly the prescribed equivalence relation. -/
theorem toHom_eq_toHom_iff [IsNoetherian R M] [IsNoetherian R N] (q : Pair R e M N) :
    p.toHom = q.toHom ↔ Rel p q := by
  constructor
  · intro h
    obtain ⟨W, hW, hWp, hWq, he⟩ := Quotient.exact h
    let U := (p.domain ⊓ q.domain) ⊓ W.comap (smallRadical R e M).mkQ
    refine ⟨U, (p.dense_domain.inf q.dense_domain).inf (hW.comap _),
      inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right,
      smallRadical R e N, small_smallRadical, le_smallRadical p.small_target,
      le_smallRadical q.small_target, ?_⟩
    intro x
    have h := he ⟨(smallRadical R e M).mkQ x, x.property.2⟩
    change p.targetMap ⟨x, x.property.1.1⟩ = q.targetMap ⟨x, x.property.1.2⟩
    rw [← p.normalize_apply ⟨x, x.property.1.1⟩,
      ← q.normalize_apply ⟨x, x.property.1.2⟩]
    exact h
  · rintro ⟨U, hU, hUp, hUq, T, hT, hpT, hqT, he⟩
    apply Quotient.sound
    refine ⟨U.map (smallRadical R e M).mkQ,
      hU.map _ (Submodule.mkQ_surjective _), Submodule.map_mono hUp,
      Submodule.map_mono hUq, ?_⟩
    rintro ⟨_, y, hy, rfl⟩
    change p.normalize.val (p.domainMap ⟨y, hUp hy⟩) =
      q.normalize.val (q.domainMap ⟨y, hUq hy⟩)
    rw [p.normalize_apply, q.normalize_apply]
    have h := congrArg (Submodule.mapQ T (smallRadical R e N) LinearMap.id
      (le_smallRadical hT)) (he ⟨y, hy⟩)
    simpa only [targetMap, LinearMap.comp_apply, enlarge_trans] using h

/-- Every normalized germ comes from a pair in the original modules. -/
theorem toHom_surjective [IsNoetherian R M] [IsNoetherian R N] :
    Function.Surjective (fun p : Pair R e M N => p.toHom) := by
  intro h
  refine Quotient.inductionOn (motive := fun h => ∃ p : Pair R e M N, p.toHom = h) h ?_
  intro f
  let U := f.val.domain.comap (smallRadical R e M).mkQ
  let a : U →ₗ[R] f.val.domain :=
    { toFun := fun x => ⟨(smallRadical R e M).mkQ x, x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : Pair R e M N :=
    ⟨U, f.property.comap _, smallRadical R e N, small_smallRadical, f.val.toFun.comp a⟩
  refine ⟨p, Quotient.sound (Representative.rel_of_eq _ _ ?_)⟩
  intro x hp hf
  obtain ⟨y, hy, he⟩ := hp
  have hx : (⟨x, ⟨y, hy, he⟩⟩ : p.normalize.val.domain) = p.domainMap ⟨y, hy⟩ :=
    Subtype.ext he.symm
  rw [hx, p.normalize_apply]
  change Submodule.mapQ (smallRadical R e N) (smallRadical R e N) LinearMap.id le_rfl
    (f.val ⟨(smallRadical R e M).mkQ y, hy⟩) = f.val ⟨x, hf⟩
  rw [Submodule.mapQ_id]
  change f.val ⟨(smallRadical R e M).mkQ y, hy⟩ = f.val ⟨x, hf⟩
  congr 1
  exact Subtype.ext he

end Pair

end Germ
end Module
