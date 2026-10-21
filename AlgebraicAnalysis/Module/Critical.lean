module
public import AlgebraicAnalysis.Module.LocSmall
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Order.WellFounded

@[expose] public section

/-!
# Critical modules and the small radical

All scalars act on the left; use the opposite ring for right modules.
The strict dimension stratum is `Module.Small`, including its zero convention.
The small radical API comes from `LocSmall`; its smallness uses Noetherianity,
but criticality itself does not.
-/

universe u v w

namespace Module

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- A nonzero module of exact finite dimension `e` all of whose proper
nonzero-submodule quotients lie in the strict stratum below `e`. -/
structure Critical (R : Type u) (e : ℕ) (M : Type v) [Ring R]
    [AddCommGroup M] [Module R M] : Prop where
  nontrivial : Nontrivial M
  devLE : DevLE R e M
  not_small : ¬ Small R e M
  small_quotient : ∀ p : Submodule R M, p ≠ ⊥ → Small R e (M ⧸ p)

/-- Criticality transports along a linear equivalence. -/
theorem Critical.of_linearEquiv {e : ℕ} (h : Critical R e M) (f : M ≃ₗ[R] N) :
    Critical R e N := by
  have := h.nontrivial
  refine ⟨f.symm.toEquiv.nontrivial, (devLE_linearEquiv_iff e f).mp h.devLE,
    fun hs => h.not_small ((small_linearEquiv_iff e f).mpr hs), ?_⟩
  intro q hq
  have hp : q.comap (f : M →ₗ[R] N) ≠ ⊥ := by
    intro he
    have := congrArg (Submodule.map (f : M →ₗ[R] N)) he
    simp only [Submodule.map_comap_eq_of_surjective f.surjective, Submodule.map_bot] at this
    exact hq this
  exact (small_linearEquiv_iff e (Submodule.Quotient.equiv (q.comap (f : M →ₗ[R] N)) q f
    (Submodule.map_comap_eq_of_surjective f.surjective q))).mp (h.small_quotient _ hp)

/-- Criticality is invariant under linear equivalence. -/
theorem critical_linearEquiv_iff (e : ℕ) (f : M ≃ₗ[R] N) :
    Critical R e M ↔ Critical R e N :=
  ⟨fun h => h.of_linearEquiv f, fun h => h.of_linearEquiv f.symm⟩

/-- A nonzero submodule of a critical module cannot be small. -/
theorem Critical.not_small_submodule {e : ℕ} (h : Critical R e M)
    {p : Submodule R M} (hp : p ≠ ⊥) : ¬Small R e p := by
  intro hs
  exact h.not_small (Small.of_submodule_quotient p hs (h.small_quotient p hp))

/-- A Noetherian critical module has zero small radical at its own dimension. -/
theorem Critical.smallRadical_eq_bot {e : ℕ} (h : Critical R e M) [IsNoetherian R M] :
    smallRadical R e M = ⊥ := by
  by_contra he
  exact h.not_small_submodule he (small_smallRadical (e := e))

/-- Intersecting any two nonzero submodules of a critical module stays nonzero
(the usual uniformity condition). -/
theorem Critical.inf_ne_bot {e : ℕ} (h : Critical R e M)
    {p q : Submodule R M} (hp : p ≠ ⊥) (hq : q ≠ ⊥) : p ⊓ q ≠ ⊥ := by
  intro he
  have hd : Disjoint q p := disjoint_iff.mpr (by simpa [inf_comm] using he.le)
  have hi : Function.Injective (p.mkQ.comp q.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ]
    exact Submodule.disjoint_iff_comap_eq_bot.mp hd
  exact h.not_small_submodule hq ((h.small_quotient p hp).of_injective _ hi)

/-- Every nonzero submodule of a critical module is critical of the same dimension. -/
theorem Critical.submodule {e : ℕ} (h : Critical R e M)
    (p : Submodule R M) (hp : p ≠ ⊥) : Critical R e p := by
  refine ⟨p.nontrivial_iff_ne_bot.mpr hp, h.devLE.submodule p,
    h.not_small_submodule hp, ?_⟩
  intro q hq
  have hmap : q.map p.subtype ≠ ⊥ := by
    intro he
    have := congrArg (Submodule.comap p.subtype) he
    simp only [Submodule.comap_map_eq_of_injective (f := p.subtype) Subtype.val_injective,
      Submodule.comap_bot, Submodule.ker_subtype] at this
    exact hq this
  let f := q.mapQ (q.map p.subtype) p.subtype (Submodule.le_comap_map _ _)
  have hi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ,
      Submodule.comap_map_eq_of_injective Subtype.val_injective]
    exact Submodule.mkQ_map_self q
  exact (h.small_quotient _ hmap).of_injective f hi

/-- Dimension-zero criticality is ordinary simplicity. -/
theorem critical_zero_of_isSimpleModule [IsSimpleModule R M] : Critical R 0 M := by
  have := IsSimpleModule.nontrivial R M
  refine ⟨inferInstance, (by
      intro c hc
      by_cases hz : ∃ i, c i = ⊥
      · obtain ⟨i, hi⟩ := hz
        exact ⟨i, fun j hj => (le_bot_iff.mp (hi ▸ hc hj)).trans hi.symm⟩
      · push Not at hz
        exact ⟨0, fun i _ => ((eq_bot_or_eq_top (c i)).resolve_left (hz i)).trans
          ((eq_bot_or_eq_top (c 0)).resolve_left (hz 0)).symm⟩),
    fun h => not_subsingleton M h, ?_⟩
  intro p hp
  have : p = ⊤ := (eq_bot_or_eq_top p).resolve_left hp
  subst p
  exact small_of_subsingleton 0

/-- A finite-deviation bound makes the relation of having a non-small
successive quotient well-founded. This is the termination argument for
critical-submodule descent. -/
theorem DevLE.wellFounded_not_small_quotient {e : ℕ} (h : DevLE R e M) :
    WellFounded (fun q p : Submodule R M =>
      q ≤ p ∧ ¬Small R e (p ⧸ q.comap p.subtype)) := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  refine ⟨fun ⟨c, hc⟩ => ?_⟩
  have hanti : Antitone c := antitone_nat_of_succ_le (fun i => (hc i).1)
  cases e with
  | zero =>
    obtain ⟨i, hi⟩ := h c hanti
    have he : c (i + 1) = c i := hi _ (Nat.le_succ i)
    apply (hc i).2
    rw [he]
    have : (c i).comap (c i).subtype = ⊤ := Submodule.comap_subtype_self _
    rw [this]
    exact small_of_subsingleton 0
  | succ e =>
    obtain ⟨i, hi⟩ := (devLE_succ_iff e).mp h c hanti
    exact (hc i).2 (hi i le_rfl)

/-- In a module with no nonzero small submodule, finite deviation produces
an `e`-critical submodule. No Noetherian assumption is needed for descent. -/
theorem DevLE.exists_critical_submodule_of_pure {e : ℕ} (h : DevLE R e M)
    [Nontrivial M] (hpure : ∀ p : Submodule R M, p ≠ ⊥ → ¬Small R e p) :
    ∃ p : Submodule R M, Critical R e p := by
  obtain ⟨p, hp, hmin⟩ := h.wellFounded_not_small_quotient.has_min
    {p : Submodule R M | p ≠ ⊥} ⟨⊤, top_ne_bot⟩
  refine ⟨p, p.nontrivial_iff_ne_bot.mpr hp, h.submodule p, hpure p hp, ?_⟩
  intro q hq
  by_contra hs
  have hmap : q.map p.subtype ≠ ⊥ := by
    intro he
    apply hq
    have := congrArg (Submodule.comap p.subtype) he
    simpa only [Submodule.comap_map_eq_of_injective (f := p.subtype)
      Subtype.val_injective, Submodule.comap_bot, Submodule.ker_subtype] using this
  apply hmin (q.map p.subtype) hmap
  refine ⟨Submodule.map_subtype_le p q, ?_⟩
  rw [Submodule.comap_map_eq_of_injective (f := p.subtype) Subtype.val_injective]
  exact hs

/-- There is a critical submodule of the least dimension occurring among
nonzero submodules. In particular its dimension is at most the given bound.
The result is stronger than the Noetherian version: descent alone suffices. -/
theorem DevLE.exists_critical_submodule_minimal {n : ℕ} (h : DevLE R n M)
    [Nontrivial M] : ∃ e ≤ n, ∃ p : Submodule R M, Critical R e p ∧
      ∀ (q : Submodule R M), q ≠ ⊥ → ∀ d, DevLE R d q → e ≤ d := by
  classical
  have hex : ∃ e, ∃ p : Submodule R M, p ≠ ⊥ ∧ DevLE R e p :=
    ⟨n, ⊤, top_ne_bot, h.submodule ⊤⟩
  let e := Nat.find hex
  obtain ⟨a, ha, hda⟩ := Nat.find_spec hex
  have hleast : ∀ (q : Submodule R M), q ≠ ⊥ → ∀ d, DevLE R d q → e ≤ d := by
    intro q hq d hd
    exact Nat.find_min' hex ⟨q, hq, hd⟩
  have hpure : ∀ q : Submodule R a, q ≠ ⊥ → ¬Small R e q := by
    intro q hq hs
    have hmap : q.map a.subtype ≠ ⊥ := by
      intro he
      apply hq
      have := congrArg (Submodule.comap a.subtype) he
      simpa only [Submodule.comap_map_eq_of_injective (f := a.subtype)
        Subtype.val_injective, Submodule.comap_bot, Submodule.ker_subtype] using this
    cases he : e with
    | zero => exact hq (Submodule.subsingleton_iff_eq_bot.mp (by simpa only [he, small_zero_iff] using hs))
    | succ d =>
      have hd : DevLE R d (q.map a.subtype) :=
        (devLE_linearEquiv_iff d (Submodule.equivMapOfInjective a.subtype
          Subtype.val_injective q)).mp (by simpa only [he, small_succ_iff] using hs)
      have := hleast _ hmap d hd
      omega
  have := a.nontrivial_iff_ne_bot.mpr ha
  obtain ⟨p, hp⟩ := hda.exists_critical_submodule_of_pure hpure
  exact ⟨e, Nat.find_min' hex ⟨⊤, top_ne_bot, h.submodule ⊤⟩,
    p.map a.subtype, hp.of_linearEquiv
      (Submodule.equivMapOfInjective a.subtype Subtype.val_injective p), hleast⟩

/-- Every nonzero finite-deviation module has a critical submodule. -/
theorem DevLE.exists_critical_submodule {n : ℕ} (h : DevLE R n M) [Nontrivial M] :
    ∃ e ≤ n, ∃ p : Submodule R M, Critical R e p := by
  obtain ⟨e, he, p, hp, _⟩ := h.exists_critical_submodule_minimal
  exact ⟨e, he, p, hp⟩

end Module
