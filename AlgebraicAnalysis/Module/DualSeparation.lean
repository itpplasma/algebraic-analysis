module
public import AlgebraicAnalysis.Module.GermSchur
public import AlgebraicAnalysis.Module.CriticalFiltration
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-!
# Critical quotients and dual separation

The separation theorem here concerns a critical target. Finite critical-type
separation for a general Noetherian finite-deviation module requires further
restriction and finite-dimensionality arguments.

These are new proofs for generalized-stafford's
`.lake/research/active/formal-scope-BC.md`, step 7; no source-code extraction
or downstream declaration replacement is involved.
-/

universe u v w

namespace Module

variable {R : Type u} [Ring R] {e : ℕ}
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A non-small Noetherian module of deviation at most `e` has an
`e`-critical quotient. The quotient is obtained by maximality, not by
critical-submodule descent. -/
theorem DevLE.exists_critical_quotient [IsNoetherian R M]
    (hM : DevLE R e M) (hne : ¬Small R e M) :
    ∃ p : Submodule R M, Critical R e (M ⧸ p) := by
  classical
  have hbot : ¬Small R e (M ⧸ (⊥ : Submodule R M)) := by
    intro hs
    exact hne ((small_linearEquiv_iff e
      ((⊥ : Submodule R M).quotEquivOfEqBot rfl)).mp hs)
  obtain ⟨p, hp, hmax⟩ := wellFounded_gt.has_min
    {p : Submodule R M | ¬Small R e (M ⧸ p)} ⟨⊥, hbot⟩
  have hn : Nontrivial (M ⧸ p) := not_subsingleton_iff_nontrivial.mp
    (fun hs => hp (by let := hs; exact small_of_subsingleton e))
  refine ⟨p, hn, hM.quotient p, hp, ?_⟩
  intro q hq
  let t := q.comap p.mkQ
  have hpt : p ≤ t := Submodule.le_comap_mkQ _ _
  have heq : t.map p.mkQ = q :=
    Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective p) q
  have hlt : p < t := lt_of_le_of_ne hpt (by
    intro he
    have he' := congrArg (Submodule.map p.mkQ) he
    rw [Submodule.mkQ_map_self, heq] at he'
    exact hq he'.symm)
  have ht : Small R e (M ⧸ t) := by
    by_contra ht
    exact hmax t ht hlt
  have hs := (small_linearEquiv_iff e
    (Submodule.quotientQuotientEquivQuotient p t hpt)).mpr ht
  rwa [heq] at hs

namespace Germ.Hom

variable {C : Type w} [AddCommGroup C] [Module R C] [IsNoetherian R C]

/-- Evaluation at a germ is linear over the target's germ endomorphisms. -/
def compLinear (x : Hom R e M C) : End R e C →ₗ[End R e C] Hom R e M C where
  toFun h := comp h x
  map_add' h g := add_comp h g x
  map_smul' a h := comp_assoc a h x

/-- A nonzero germ between critical modules identifies its dual Hom with
the target's Schur ring by composition. -/
theorem compLinear_bijective_of_critical [IsNoetherian R M]
    (hM : Critical R e M) (hC : Critical R e C) (x : Hom R e M C) (hx : x ≠ 0) :
    Function.Bijective (compLinear x) := by
  obtain ⟨y, hyx, hxy⟩ := exists_inverse_of_critical hM hC x hx
  constructor
  · intro f g he
    have h := congrArg (fun z : Hom R e M C => comp z y) he
    change comp (comp f x) y = comp (comp g x) y at h
    simpa only [comp_assoc, hxy, comp_id] using h
  · intro f
    refine ⟨comp f y, ?_⟩
    change comp (comp f y) x = f
    rw [comp_assoc, hyx, comp_id]

/-- For critical source and target, the Schur Hom space is finite. -/
theorem finite_of_critical [IsNoetherian R M]
    (hM : Critical R e M) (hC : Critical R e C) :
    Module.Finite (End R e C) (Hom R e M C) := by
  classical
  by_cases hs : Subsingleton (Hom R e M C)
  · let := hs
    infer_instance
  · have := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨x, hx⟩ := exists_ne (0 : Hom R e M C)
    exact Module.Finite.of_surjective (compLinear x)
      (compLinear_bijective_of_critical hM hC x hx).surjective

/-- A critical factor contributes at most one Schur dimension. -/
theorem finrank_le_one_of_critical [IsNoetherian R M]
    (hM : Critical R e M) (hC : Critical R e C) :
    letI := End.divisionRing hC
    Module.finrank (End R e C) (Hom R e M C) ≤ 1 := by
  classical
  let := End.divisionRing hC
  by_cases hs : Subsingleton (Hom R e M C)
  · let := hs
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  · have := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨x, hx⟩ := exists_ne (0 : Hom R e M C)
    have h := LinearMap.finrank_le_finrank_of_surjective (f := compLinear x)
      (compLinear_bijective_of_critical hM hC x hx).surjective
    simpa only [Module.finrank_self] using h

/-- A germ into a critical module is epic exactly when it is nonzero. -/
theorem epic_iff_ne_zero_of_critical (hC : Critical R e C) (x : Hom R e M C) :
    Epic x ↔ x ≠ 0 := by
  refine ⟨?_, PartialHom.epic_of_ne_zero_of_critical (critical_quotient_smallRadical hC) x⟩
  intro hx hz
  rw [hz] at hx
  have hs : Small R e (C ⧸ smallRadical R e C) := by
    change Dense R e (0 : Representative R e
      (M ⧸ smallRadical R e M) (C ⧸ smallRadical R e C)).val.toFun.range at hx
    have hr : (0 : Representative R e
      (M ⧸ smallRadical R e M) (C ⧸ smallRadical R e C)).val.toFun.range = ⊥ :=
      LinearMap.range_zero
    rw [hr] at hx
    exact (small_linearEquiv_iff e
      ((⊥ : Submodule R (C ⧸ smallRadical R e C)).quotEquivOfEqBot rfl)).mp hx
  exact (critical_quotient_smallRadical hC).not_small hs

/-- Critical-target dual separation: testing against the target's own
Schur space suffices, for a germ with any source. -/
theorem epic_iff_injective_comp_of_critical (hC : Critical R e C) (x : Hom R e M C) :
    Epic x ↔ Function.Injective (fun h : End R e C => comp h x) := by
  refine ⟨fun hx g h he => hx.right_cancel g h he, ?_⟩
  intro hi
  apply (epic_iff_ne_zero_of_critical hC x).mpr
  intro hz
  have he : comp (id : End R e C) x = comp (0 : End R e C) x := by
    rw [hz]
    exact (PartialHom.comp_zero _).trans (PartialHom.zero_comp _).symm
  have hid := hi he
  let : DivisionRing (End R e C) := End.divisionRing hC
  exact one_ne_zero hid

end Germ.Hom
end Module
