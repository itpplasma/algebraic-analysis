module
public import AlgebraicAnalysis.Module.Deviation
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

/-!
# Locally small modules and dense submodules

All modules are left modules over an arbitrary ring; use the opposite ring for
right modules. Local smallness tests finitely generated submodules, rather than
asserting a deviation bound on an infinite direct sum. Extension closure uses
a Noetherian scalar ring. The small radical is small for Noetherian modules.

These are new proofs for the interfaces in generalized-stafford's research
notes `docs/intrinsic-finite-krull.md`, §2, and
`.lake/research/active/formal-scope-BC.md`, steps 2 and 4; no source-code
extraction or downstream declaration replacement is involved.
-/

universe u v w

open scoped DirectSum

namespace Module

variable (R : Type u) [Ring R] (e : ℕ) (M : Type v) [AddCommGroup M] [Module R M]

/-- Every finitely generated submodule belongs to the strict deviation stratum. -/
def LocSmall : Prop := ∀ U : Submodule R M, U.FG → Small R e U

/-- A submodule is dense when its quotient belongs to the strict stratum. -/
def Dense {M : Type v} [AddCommGroup M] [Module R M]
    (U : Submodule R M) : Prop := Small R e (M ⧸ U)

/-- The sum of all small submodules. It is small when the ambient module is Noetherian. -/
def smallRadical : Submodule R M := ⨆ U : {U : Submodule R M // Small R e U}, U.val

variable {R e M} {N : Type w} [AddCommGroup N] [Module R N]

theorem Small.map {U : Submodule R M} (h : Small R e U) (f : M →ₗ[R] N) :
    Small R e (U.map f) :=
  h.of_surjective (f.submoduleMap U) (by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩)

theorem Small.of_le {U V : Submodule R M} (h : Small R e V) (hUV : U ≤ V) :
    Small R e U :=
  h.of_injective (Submodule.inclusion hUV) (Submodule.inclusion_injective hUV)

theorem Small.sup {U V : Submodule R M} (hU : Small R e U) (hV : Small R e V) :
    Small R e (U ⊔ V : Submodule R M) := by
  rw [Submodule.sup_eq_range]
  exact (hU.prod hV).of_surjective (U.subtype.coprod V.subtype).rangeRestrict (by rintro ⟨y, x, rfl⟩; exact ⟨x, rfl⟩)

theorem Small.finset_sup {ι : Type*} (s : Finset ι) (U : ι → Submodule R M)
    (h : ∀ i ∈ s, Small R e (U i)) : Small R e (s.sup U : Submodule R M) :=
  Finset.sup_induction (p := fun U : Submodule R M => Small R e U)
    (small_of_subsingleton e) (fun _ ha _ hb => ha.sup hb) h

/-- Pulling back a small submodule of a quotient gives a small extension. -/
theorem Small.comap_mkQ {p : Submodule R M} (hp : Small R e p)
    {q : Submodule R (M ⧸ p)} (hq : Small R e q) :
    Small R e (q.comap p.mkQ) := by
  let f : q.comap p.mkQ →ₗ[R] q :=
    (p.mkQ.comp (q.comap p.mkQ).subtype).codRestrict q (fun x => x.property)
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := p.mkQ_surjective x
    exact ⟨⟨y, hx⟩, rfl⟩
  have hk : Small R e (LinearMap.ker f) := by
    apply hp.of_injective
      (((q.comap p.mkQ).subtype.comp (LinearMap.ker f).subtype).codRestrict p ?_) ?_
    · intro x
      exact (Submodule.Quotient.mk_eq_zero p).mp
        (congrArg Subtype.val x.property)
    · intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : p => (z : M)) h
  exact (small_iff_submodule_quotient e (LinearMap.ker f)).mpr
    ⟨hk, (small_linearEquiv_iff e (f.quotKerEquivOfSurjective hf)).mpr hq⟩

theorem le_smallRadical {U : Submodule R M} (hU : Small R e U) :
    U ≤ smallRadical R e M := le_iSup (fun U : {U : Submodule R M // Small R e U} => U.val) ⟨U, hU⟩

/-- A finitely generated submodule of a sum of small submodules is small. -/
theorem small_of_fg_le_iSup {ι : Type*} (U : ι → Submodule R M)
    (hU : ∀ i, Small R e (U i)) {V : Submodule R M} (hV : V.FG)
    (hVU : V ≤ ⨆ i, U i) : Small R e V := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_compact V).mp hV |>.exists_finset_of_le_iSup U hVU
  rw [← Finset.sup_eq_iSup] at hs
  exact (Small.finset_sup s U (fun i _ => hU i)).of_le hs

theorem locSmall_smallRadical : LocSmall R e (smallRadical R e M) := by
  intro U hU
  have h := small_of_fg_le_iSup
    (fun V : {V : Submodule R M // Small R e V} => V.val) (fun V => V.property)
    (hU.map (smallRadical R e M).subtype) (Submodule.map_subtype_le _ _)
  exact h.of_injective ((smallRadical R e M).subtype.submoduleMap U)
    (by intro x y h; apply Subtype.ext; apply Subtype.ext; have hh := congrArg Subtype.val h; exact hh)

theorem Small.locSmall (h : Small R e M) : LocSmall R e M := fun U _ => h.submodule U

/-- Local smallness agrees with smallness on finitely generated modules. -/
theorem locSmall_iff_small [Module.Finite R M] : LocSmall R e M ↔ Small R e M := by
  refine ⟨fun h => ?_, Small.locSmall⟩
  exact (h ⊤ Module.Finite.fg_top).of_surjective (⊤ : Submodule R M).subtype
    (by intro x; exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩)

/-- In particular, no additional Noetherian modules are killed by local extension. -/
theorem locSmall_iff_small_of_isNoetherian [IsNoetherian R M] :
    LocSmall R e M ↔ Small R e M := locSmall_iff_small

theorem small_smallRadical [IsNoetherian R M] : Small R e (smallRadical R e M) :=
  locSmall_iff_small.mp locSmall_smallRadical

theorem LocSmall.of_injective (h : LocSmall R e N) (f : M →ₗ[R] N)
    (hf : Function.Injective f) : LocSmall R e M := by
  intro U hU
  exact (h (U.map f) (hU.map f)).of_injective (f.submoduleMap U)
    (fun x y hxy => Subtype.ext (hf (congrArg Subtype.val hxy)))

theorem LocSmall.submodule (h : LocSmall R e M) (U : Submodule R M) : LocSmall R e U :=
  h.of_injective U.subtype Subtype.val_injective

/-- Pointwise small envelopes are enough: finite generators use a finite sum of them. -/
theorem locSmall_of_small_envelopes
    (h : ∀ x : M, ∃ U : Submodule R M, Small R e U ∧ x ∈ U) : LocSmall R e M := by
  have ht : smallRadical R e M = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨U, hU, hx⟩ := h x
    exact le_smallRadical hU hx
  intro U hU
  exact small_of_fg_le_iSup
    (fun V : {V : Submodule R M // Small R e V} => V.val) (fun V => V.property)
    hU (by change U ≤ smallRadical R e M; rw [ht]; exact le_top)

theorem LocSmall.small_envelope (h : LocSmall R e M) (x : M) :
    ∃ U : Submodule R M, Small R e U ∧ x ∈ U :=
  ⟨R ∙ x, h _ (Submodule.fg_span_singleton x), Submodule.mem_span_singleton_self x⟩

theorem LocSmall.of_surjective (h : LocSmall R e M) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : LocSmall R e N := by
  apply locSmall_of_small_envelopes
  intro y
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨U, hU, hx⟩ := h.small_envelope x
  exact ⟨U.map f, hU.map f, Submodule.mem_map_of_mem hx⟩

theorem LocSmall.quotient (h : LocSmall R e M) (U : Submodule R M) :
    LocSmall R e (M ⧸ U) := h.of_surjective U.mkQ (Submodule.mkQ_surjective U)

theorem LocSmall.map {U : Submodule R M} (h : LocSmall R e U) (f : M →ₗ[R] N) :
    LocSmall R e (U.map f) :=
  h.of_surjective (f.submoduleMap U) (by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩)

/-- The Noetherian ring hypothesis controls the kernel inside each finite submodule. -/
theorem LocSmall.of_submodule_quotient [IsNoetherianRing R] (U : Submodule R M)
    (hU : LocSmall R e U) (hQ : LocSmall R e (M ⧸ U)) : LocSmall R e M := by
  intro V hV
  have : Module.Finite R V := Module.Finite.of_fg hV
  let f : V →ₗ[R] M ⧸ U := U.mkQ.comp V.subtype
  have hk : Small R e (LinearMap.ker f) := by
    have hh := hU.of_injective
      (show LinearMap.ker f →ₗ[R] U from
        { toFun := fun x => ⟨x.val.val, (Submodule.Quotient.mk_eq_zero U).mp x.property⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl })
      (by intro x y h; apply Subtype.ext; apply Subtype.ext; have hh := congrArg Subtype.val h; exact hh)
    exact locSmall_iff_small.mp hh
  have hr : Small R e (LinearMap.range f) := hQ _ (Submodule.fg_range f)
  exact Small.of_submodule_quotient (LinearMap.ker f) hk
    ((small_linearEquiv_iff e f.quotKerEquivRange).mpr hr)

/-- Arbitrary sums of locally small submodules are locally small. -/
theorem LocSmall.iSup {ι : Type*} (U : ι → Submodule R M)
    (hU : ∀ i, LocSmall R e (U i)) : LocSmall R e (⨆ i, U i : Submodule R M) := by
  have hle : (⨆ i, U i) ≤ smallRadical R e M := by
    apply iSup_le
    intro i x hx
    obtain ⟨V, hV, hmem⟩ := (hU i).small_envelope ⟨x, hx⟩
    exact le_smallRadical (hV.map (U i).subtype) (Submodule.mem_map_of_mem hmem)
  exact locSmall_smallRadical.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

/-- Arbitrary direct sums, without a finite-index hypothesis. -/
theorem LocSmall.directSum {ι : Type*} {P : ι → Type v}
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    (hP : ∀ i, LocSmall R e (P i)) : LocSmall R e (⨁ i, P i) := by
  classical
  let U (i : ι) : Submodule R (⨁ i, P i) := LinearMap.range (DirectSum.lof R ι P i)
  have hU : ∀ i, LocSmall R e (U i) := fun i =>
    (hP i).of_surjective (DirectSum.lof R ι P i).rangeRestrict (by rintro ⟨y, x, rfl⟩; exact ⟨x, rfl⟩)
  have ht : (⨆ i, U i) = ⊤ := by
    apply top_unique
    suffices ∀ x : (⨁ i, P i), x ∈ ⨆ i, U i from fun x _ => this x
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | of i x => exact le_iSup U i ⟨x, rfl⟩
  have h := LocSmall.iSup U hU
  rw [ht] at h
  exact h.of_surjective (⊤ : Submodule R (⨁ i, P i)).subtype
    (by intro x; exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩)

/-- The radical is functorial for linear maps. -/
theorem smallRadical_le_comap (f : M →ₗ[R] N) :
    smallRadical R e M ≤ (smallRadical R e N).comap f := by
  apply iSup_le
  intro U x hx
  exact le_smallRadical (U.property.map f) (Submodule.mem_map_of_mem hx)

/-- A Noetherian module modulo its radical has no nonzero small submodule. -/
theorem eq_bot_of_small_quotient_radical [IsNoetherian R M]
    (U : Submodule R (M ⧸ smallRadical R e M)) (hU : Small R e U) : U = ⊥ := by
  have hle := le_smallRadical
    ((small_smallRadical (R := R) (e := e) (M := M)).comap_mkQ hU)
  have he : U.comap (smallRadical R e M).mkQ = smallRadical R e M :=
    le_antisymm hle (Submodule.le_comap_mkQ _ _)
  have := congrArg (Submodule.map (smallRadical R e M).mkQ) he
  simpa only [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _),
    Submodule.mkQ_map_self] using this

@[simp] theorem dense_top : Dense R e (⊤ : Submodule R M) := small_of_subsingleton e

theorem Dense.mono {U V : Submodule R M} (hU : Dense R e U) (hUV : U ≤ V) :
    Dense R e V :=
  hU.of_surjective (Submodule.mapQ U V LinearMap.id hUV)
    (by intro y; obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective V y
        exact ⟨U.mkQ x, rfl⟩)

/-- Inverse images of dense submodules are dense, with no surjectivity assumption. -/
theorem Dense.comap {V : Submodule R N} (hV : Dense R e V) (f : M →ₗ[R] N) :
    Dense R e (V.comap f) := by
  let g := V.mkQ.comp f
  have hk : g.ker = V.comap f := by ext x; simp [g]
  rw [Dense, ← hk]
  exact (small_linearEquiv_iff e g.quotKerEquivRange).mpr (hV.submodule _)

/-- Surjective images of dense submodules are dense. -/
theorem Dense.map {U : Submodule R M} (hU : Dense R e U) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : Dense R e (U.map f) := by
  exact hU.of_surjective (Submodule.mapQ U (U.map f) f (Submodule.le_comap_map f U)) (by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (U.map f) y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨U.mkQ x, rfl⟩)

/-- Removing a small summand from a dense sum preserves density. -/
theorem Dense.of_small_sup {U V : Submodule R M} (h : Dense R e (U ⊔ V))
    (hU : Small R e U) : Dense R e V := by
  apply Small.of_submodule_quotient (U.map V.mkQ) (hU.map V.mkQ)
  apply (small_linearEquiv_iff e (Submodule.quotientQuotientEquivQuotientSup V U)).mpr
  rw [sup_comm V U]
  exact h

/-- Finite intersections preserve density. -/
theorem Dense.inf {U V : Submodule R M} (hU : Dense R e U) (hV : Dense R e V) :
    Dense R e (U ⊓ V) := by
  let f := U.mkQ.prod V.mkQ
  have hk : LinearMap.ker f = U ⊓ V := by ext x; simp [f]
  rw [Dense, ← hk]
  exact (small_linearEquiv_iff e f.quotKerEquivRange).mpr ((hU.prod hV).submodule _)

/-- Density composes for nested submodules. -/
theorem Dense.map_subtype {U : Submodule R M} (hU : Dense R e U)
    {V : Submodule R U} (hV : Dense R e V) : Dense R e (V.map U.subtype) := by
  let W := V.map U.subtype
  let f : M ⧸ W →ₗ[R] M ⧸ U := Submodule.mapQ W U LinearMap.id
    (Submodule.map_subtype_le U V)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective U y
    exact ⟨W.mkQ x, rfl⟩
  have hr : Small R e (LinearMap.ker f) := by
    let g : U →ₗ[R] LinearMap.ker f :=
      { toFun := fun x => ⟨W.mkQ x, by simp [f]⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hg : V ≤ LinearMap.ker g := by
      intro x hx
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero W).mpr ⟨x, hx, rfl⟩
    apply hV.of_surjective (V.liftQ g hg)
    intro y
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective W y.val
    have hxu : x ∈ U := (Submodule.Quotient.mk_eq_zero U).mp (by
      have : f y.val = 0 := y.property
      rw [← hx] at this
      exact this)
    exact ⟨V.mkQ ⟨x, hxu⟩, Subtype.ext hx⟩
  exact Small.of_submodule_quotient (LinearMap.ker f) hr
    ((small_linearEquiv_iff e (f.quotKerEquivOfSurjective hf)).mpr hU)

end Module
