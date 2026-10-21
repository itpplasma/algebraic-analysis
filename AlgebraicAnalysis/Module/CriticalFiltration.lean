module
public import AlgebraicAnalysis.Module.Critical
public import Mathlib.Order.RelSeries
public import Mathlib.Order.ModularLattice
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Finite critical filtrations

A filtration is an actual finite ascending series of submodules from zero to
 the whole module, with critical successive quotient modules. Dimensions need
not be ordered. Scalars may be noncommutative.
-/

universe u v

open scoped Classical

namespace Module

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A critical step with an explicit common finite dimension ceiling. -/
def CriticalStep (R : Type u) (n : ℕ) (M : Type v) [Ring R]
    [AddCommGroup M] [Module R M] (p q : Submodule R M) : Prop :=
  p ≤ q ∧ ∃ d ≤ n, Critical R d (q ⧸ p.comap q.subtype)

/-- A finite critical filtration, including its zero and whole-module endpoints. -/
structure CriticalFiltration (R : Type u) (n : ℕ) (M : Type v) [Ring R]
    [AddCommGroup M] [Module R M] extends RelSeries {(p, q) | CriticalStep R n M p q} where
  head_eq_bot : toRelSeries.head = ⊥
  last_eq_top : toRelSeries.last = ⊤

/-- A lifted submodule of a quotient has precisely the expected factor. -/
noncomputable def comapMkQFactorEquiv (p : Submodule R M)
    (a : Submodule R (M ⧸ p)) :
    (a.comap p.mkQ ⧸ p.comap (a.comap p.mkQ).subtype) ≃ₗ[R] a := by
  let f : a.comap p.mkQ →ₗ[R] a :=
    (p.mkQ.comp (a.comap p.mkQ).subtype).codRestrict a (fun x => x.property)
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := p.mkQ_surjective x
    exact ⟨⟨y, hx⟩, rfl⟩
  have hk : f.ker = p.comap (a.comap p.mkQ).subtype := by
    ext x
    change (⟨p.mkQ x.val, x.property⟩ : a) = 0 ↔ x.val ∈ p
    rw [Subtype.ext_iff]
    exact Submodule.Quotient.mk_eq_zero p
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)

/-- Noetherian induction on submodules terminates the construction of critical
factors in successive quotients. -/
theorem DevLE.nonempty_criticalFiltration {n : ℕ} (h : DevLE R n M)
    [IsNoetherian R M] : Nonempty (CriticalFiltration R n M) := by
  classical
  have aux : ∀ p : Submodule R M, ∃ s : RelSeries {(p, q) | CriticalStep R n M p q},
      s.head = p ∧ s.last = ⊤ := by
    intro p
    induction p using (wellFounded_gt : WellFounded ((· > ·) :
        Submodule R M → Submodule R M → Prop)).induction with
    | h p ih =>
      by_cases hp : p = ⊤
      · exact ⟨RelSeries.singleton _ p, rfl, hp⟩
      · have : Nontrivial (M ⧸ p) := Submodule.Quotient.nontrivial_iff.mpr hp
        obtain ⟨d, hd, a, ha⟩ := (h.quotient p).exists_critical_submodule
        let q := a.comap p.mkQ
        have hpq : p < q := by
          refine lt_of_le_of_ne (Submodule.le_comap_mkQ _ _) ?_
          intro he
          have hbot : a = ⊥ := by
            have := congrArg (Submodule.map p.mkQ) he
            simpa only [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _),
              Submodule.mkQ_map_self, q] using this.symm
          exact (a.nontrivial_iff_ne_bot.mp ha.nontrivial) hbot
        obtain ⟨s, hs, ht⟩ := ih q hpq
        have hstep : CriticalStep R n M p s.head := by
          rw [hs]
          exact ⟨hpq.le, d, hd, ha.of_linearEquiv (comapMkQFactorEquiv p a).symm⟩
        exact ⟨s.cons p hstep, by simp, by simpa using ht⟩
  obtain ⟨s, hs, ht⟩ := aux ⊥
  exact ⟨⟨s, hs, ht⟩⟩

/- The following order helpers keep the chain-length argument independent
of choices of representatives in quotient modules. -/
private def OrderSmall (e : ℕ) (α : Type*) [PartialOrder α] : Prop :=
  match e with
  | 0 => Subsingleton α
  | d + 1 => Order.DevLE d α

private theorem OrderSmall.of_strictMono {α β : Type*} [PartialOrder α]
    [PartialOrder β] {e : ℕ} (h : OrderSmall e β) {f : α → β} (hf : StrictMono f)
    (hi : Function.Injective f) : OrderSmall e α := by
  cases e with
  | zero => exact ⟨fun x y => hi (h.elim _ _)⟩
  | succ d => exact Order.DevLE.of_strictMono h hf

private theorem OrderSmall.prod {α β : Type*} [PartialOrder α] [PartialOrder β]
    {e : ℕ} (h : OrderSmall e α) (k : OrderSmall e β) : OrderSmall e (α × β) := by
  cases e with
  | zero => exact ⟨fun x y => Prod.ext (h.elim _ _) (k.elim _ _)⟩
  | succ d => exact Order.DevLE.prod h k

private theorem orderSmall_submodule_iff (e : ℕ) :
    OrderSmall e (Submodule R M) ↔ Small R e M := by
  cases e with
  | zero =>
    constructor
    · intro h
      have he : (⊤ : Submodule R M) = ⊥ := h.elim _ _
      have hz : ∀ x : M, x = 0 := fun x => by
        have hx : x ∈ (⊥ : Submodule R M) := he ▸ Submodule.mem_top
        exact hx
      exact ⟨fun x y => (hz x).trans (hz y).symm⟩
    · intro h
      have : Subsingleton M := h
      exact (inferInstance : Subsingleton (Submodule R M))
  | succ d => rfl

private theorem orderSmall_interval_iff (e : ℕ) {a b : Submodule R M} (hab : a ≤ b) :
    OrderSmall e (Set.Icc a b) ↔ Small R e (b ⧸ a.comap b.subtype) := by
  let f := Submodule.quotientIntervalOrderIso a b hab
  rw [← orderSmall_submodule_iff]
  exact ⟨fun h => h.of_strictMono f.strictMono f.injective,
    fun h => h.of_strictMono f.symm.strictMono f.symm.injective⟩

private theorem OrderSmall.subinterval {e : ℕ} {a b x y : Submodule R M}
    (h : OrderSmall e (Set.Icc a b)) (hax : a ≤ x) (hyb : y ≤ b) :
    OrderSmall e (Set.Icc x y) := by
  let f : Set.Icc x y → Set.Icc a b :=
    fun z => ⟨z.val, hax.trans z.property.1, z.property.2.trans hyb⟩
  exact h.of_strictMono (f := f) (fun _ _ h => h)
    (fun _ _ h => Subtype.ext (congrArg (fun t : Set.Icc a b => t.val) h))

private theorem critical_upper_interval_small {e : ℕ} {a b x : Submodule R M}
    (hab : a ≤ b) (h : Critical R e (b ⧸ a.comap b.subtype))
    (hax : a < x) (hxb : x ≤ b) : OrderSmall e (Set.Icc x b) := by
  let f := Submodule.quotientIntervalOrderIso a b hab
  let q := f.symm ⟨x, hax.le, hxb⟩
  have hq : q ≠ ⊥ := by
    intro he
    have ha : f.symm ⟨a, le_rfl, hab⟩ = ⊥ := by
      apply le_bot_iff.mp
      have hh : (⟨a, le_rfl, hab⟩ : Set.Icc a b) ≤ f ⊥ := (f ⊥).property.1
      simpa only [f.symm_apply_apply] using f.symm.monotone hh
    have hh : f.symm (⟨a, le_rfl, hab⟩ : Set.Icc a b) < q := f.symm.strictMono hax
    rw [ha, he] at hh
    exact (lt_irrefl _ hh)
  have hs := (orderSmall_submodule_iff e).mpr (h.small_quotient q hq)
  let g : Set.Icc x b → Submodule R ((b ⧸ a.comap b.subtype) ⧸ q) := fun z =>
    (Submodule.comapMkQRelIso q).symm
      ⟨f.symm ⟨z.val, hax.le.trans z.property.1, z.property.2⟩,
        f.symm.monotone z.property.1⟩
  have hg : StrictMono g := fun z w hzw =>
    (Submodule.comapMkQRelIso q).symm.strictMono (f.symm.strictMono hzw)
  have hi : Function.Injective g := by
    intro z w hzw
    have hh := (Submodule.comapMkQRelIso q).symm.injective hzw
    have hh' := congrArg Subtype.val hh
    exact Subtype.ext (congrArg (fun t : Set.Icc a b => t.val) (f.symm.injective hh'))
  exact hs.of_strictMono hg hi

/-- A bounded monotone integer rank which detects every non-small interval. -/
private def IntervalRank (e : ℕ) (a b : Submodule R M) (l : ℕ) : Prop :=
  ∃ r : Set.Icc a b → ℕ, Monotone r ∧ (∀ x, r x ≤ l) ∧
    ∀ x y, x ≤ y → r x = r y → OrderSmall e (Set.Icc x.val y.val)

private theorem intervalRank_small {e : ℕ} {a b : Submodule R M}
    (h : OrderSmall e (Set.Icc a b)) : IntervalRank e a b 0 := by
  exact ⟨fun _ => 0, fun _ _ _ => le_rfl, fun _ => le_rfl,
    fun x y _ _ => h.subinterval x.property.1 y.property.2⟩

private theorem intervalRank_critical {e : ℕ} {a b : Submodule R M}
    (hab : a ≤ b) (h : Critical R e (b ⧸ a.comap b.subtype)) :
    IntervalRank e a b 1 := by
  classical
  let r : Set.Icc a b → ℕ := fun x => if x.val = a then 0 else 1
  have hr : Monotone r := by
    intro x y hxy
    change x.val ≤ y.val at hxy
    dsimp [r]
    split_ifs with hx hy hy
    · omega
    · omega
    · exact False.elim (hx (le_antisymm (hxy.trans_eq hy) x.property.1))
    · omega
  refine ⟨r, hr, fun x => by dsimp [r]; split_ifs <;> omega, ?_⟩
  intro x y hxy he
  by_cases hx : x.val = a
  · have hy : y.val = a := by
      by_contra hy
      simp [r, hx, hy] at he
    have hsmall : OrderSmall e (Set.Icc a a) := by
      cases e with
      | zero => exact (inferInstance : Subsingleton (Set.Icc a a))
      | succ d => exact Order.devLE_of_subsingleton d
    change OrderSmall e (Set.Icc x.val y.val)
    rw [hx, hy]
    exact hsmall
  · exact (critical_upper_interval_small hab h
      (lt_of_le_of_ne x.property.1 (Ne.symm hx)) x.property.2).subinterval
        le_rfl y.property.2

private theorem intervalRank_add {e l k : ℕ} {a c b : Submodule R M}
    (hac : a ≤ c) (hcb : c ≤ b) (h : IntervalRank e a c l)
    (k' : IntervalRank e c b k) : IntervalRank e a b (l + k) := by
  obtain ⟨r, hr, hrl, hre⟩ := h
  obtain ⟨s, hs, hsk, hse⟩ := k'
  let lo : Set.Icc a b → Set.Icc a c := fun x =>
    ⟨x.val ⊓ c, le_inf x.property.1 hac, inf_le_right⟩
  let hi : Set.Icc a b → Set.Icc c b := fun x =>
    ⟨x.val ⊔ c, le_sup_right, sup_le x.property.2 hcb⟩
  have hlo : Monotone lo := fun _ _ h => inf_le_inf_right c h
  have hhi : Monotone hi := fun x y h =>
    show x.val ⊔ c ≤ y.val ⊔ c from sup_le_sup_right (show x.val ≤ y.val from h) c
  refine ⟨fun x => r (lo x) + s (hi x),
    fun x y hxy => Nat.add_le_add (hr (hlo hxy)) (hs (hhi hxy)),
    fun x => Nat.add_le_add (hrl _) (hsk _), ?_⟩
  intro x y hxy he
  change r (lo x) + s (hi x) = r (lo y) + s (hi y) at he
  have helo : r (lo x) = r (lo y) := by
    have := hr (hlo hxy)
    have := hs (hhi hxy)
    omega
  have hehi : s (hi x) = s (hi y) := by
    have := hr (hlo hxy)
    have := hs (hhi hxy)
    omega
  have hprod := (hre _ _ (hlo hxy) helo).prod (hse _ _ (hhi hxy) hehi)
  let f : Set.Icc x.val y.val →
      Set.Icc (x.val ⊓ c) (y.val ⊓ c) × Set.Icc (x.val ⊔ c) (y.val ⊔ c) := fun z =>
    (⟨z.val ⊓ c, inf_le_inf_right c z.property.1, inf_le_inf_right c z.property.2⟩,
      ⟨z.val ⊔ c, sup_le_sup_right z.property.1 c, sup_le_sup_right z.property.2 c⟩)
  have hf : StrictMono f := fun z w h =>
    show f z < f w from (strictMono_inf_prod_sup (z := c) (show z.val < w.val from h))
  cases e with
  | zero =>
    have hxy' : x.val = y.val := by
      by_contra hne
      have hlt := hf (show (⟨x.val, le_rfl, hxy⟩ : Set.Icc x.val y.val) <
          ⟨y.val, hxy, le_rfl⟩ from lt_of_le_of_ne hxy (fun h => hne (congrArg (fun z : Set.Icc x.val y.val => z.val) h)))
      exact (ne_of_lt hlt) (hprod.elim _ _)
    rw [hxy']
    exact (inferInstance : Subsingleton (Set.Icc y.val y.val))
  | succ d => exact Order.DevLE.of_strictMono hprod hf


private noncomputable def stepWeight (e : ℕ) (a b : Submodule R M) : ℕ := by
  classical
  exact if Small R e (b ⧸ a.comap b.subtype) then 0 else 1

private noncomputable def seriesWeight (e : ℕ)
    (s : RelSeries {(a, b) | CriticalStep R e M a b}) : ℕ :=
  ∑ i : Fin s.length, stepWeight e (s i.castSucc) (s i.succ)

private theorem intervalRank_step {e : ℕ} {a b : Submodule R M}
    (h : CriticalStep R e M a b) : IntervalRank e a b (stepWeight e a b) := by
  classical
  by_cases hs : Small R e (b ⧸ a.comap b.subtype)
  · simpa only [stepWeight, ite_eq_left hs] using
      intervalRank_small ((orderSmall_interval_iff e h.1).mpr hs)
  · obtain ⟨d, hd, hc⟩ := h.2
    have he : e ≤ d := by
      by_contra he
      have hsmall : Small R (d + 1) (b ⧸ a.comap b.subtype) := hc.devLE
      exact hs (hsmall.mono (Nat.succ_le_of_lt (Nat.lt_of_not_ge he)))
    have hde : d = e := le_antisymm hd he
    subst d
    simpa only [stepWeight, ite_eq_right hs] using intervalRank_critical h.1 hc

set_option backward.isDefEq.respectTransparency false in
private theorem seriesWeight_snoc {e : ℕ}
    (s : RelSeries {(a, b) | CriticalStep R e M a b}) (b : Submodule R M)
    (h : CriticalStep R e M s.last b) :
    seriesWeight e (s.snoc b h) = seriesWeight e s + stepWeight e s.last b := by
  unfold seriesWeight
  change (∑ i : Fin (s.length + 1),
    stepWeight e ((s.snoc b h) i.castSucc) ((s.snoc b h) i.succ)) = _
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hi : (Fin.castSucc i).succ = Fin.castSucc i.succ := rfl
    rw [hi, RelSeries.snoc_castSucc, RelSeries.snoc_castSucc]
  · rw [RelSeries.snoc_castSucc]
    change stepWeight e s.last ((s.snoc b h) (Fin.last (s.length + 1))) = _
    rw [RelSeries.last_snoc']

set_option backward.isDefEq.respectTransparency false in
private theorem intervalRank_series {e : ℕ}
    (s : RelSeries {(a, b) | CriticalStep R e M a b}) :
    IntervalRank e s.head s.last (seriesWeight e s) := by
  induction s using RelSeries.inductionOn' with
  | singleton a =>
    have hs : OrderSmall e (Set.Icc a a) := by
      cases e with
      | zero => exact (inferInstance : Subsingleton (Set.Icc a a))
      | succ d => exact Order.devLE_of_subsingleton d
    simpa [seriesWeight] using intervalRank_small hs
  | snoc s b h ih =>
    have hmono : Monotone s := Fin.monotone_iff_le_succ.mpr (fun i => (s.step i).1)
    have hac : s.head ≤ s.last := hmono (Fin.zero_le _)
    have hr := intervalRank_add hac h.1 ih (intervalRank_step h)
    simpa only [RelSeries.head_snoc, RelSeries.last_snoc, seriesWeight_snoc] using hr

namespace CriticalFiltration

variable {n : ℕ} (F : CriticalFiltration R n M)

/-- The quotient module at one step. -/
abbrev Factor (i : Fin F.length) :=
  F.toRelSeries i.succ ⧸
    (F.toRelSeries i.castSucc).comap (F.toRelSeries i.succ).subtype

/-- Every factor has a critical dimension bounded by the ceiling. -/
theorem factor_critical (i : Fin F.length) : ∃ d ≤ n, Critical R d (F.Factor i) :=
  (F.step i).2

/-- The series is ascending. -/
theorem monotone : Monotone F.toRelSeries :=
  (Fin.monotone_iff_le_succ).mpr (fun i => (F.step i).1)

/-- Critical factors are nonzero, hence the series is strictly ascending. -/
theorem strictMono : StrictMono F.toRelSeries := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  refine lt_of_le_of_ne (F.step i).1 ?_
  intro he
  obtain ⟨d, _, hd⟩ := F.factor_critical i
  have hz : (F.toRelSeries i.castSucc).comap (F.toRelSeries i.succ).subtype = ⊤ := by
    rw [he]
    exact Submodule.comap_subtype_self _
  exact hd.not_small (by
    change Small R d (F.toRelSeries i.succ ⧸ _)
    rw [hz]
    exact small_of_subsingleton d)

/-- The number of factors surviving the strict stratum `e`. -/
noncomputable def topLength (e : ℕ) : ℕ := by
  classical
  exact ∑ i : Fin F.length, if Small R e (F.Factor i) then 0 else 1

/-- Lower-dimensional factors vanish; critical factors of dimension at least
`e` survive. This also fixes the stratum indexing at zero. -/
theorem factor_not_small_iff (i : Fin F.length) {d e : ℕ}
    (hd : Critical R d (F.Factor i)) : ¬Small R e (F.Factor i) ↔ e ≤ d := by
  constructor
  · intro hs
    by_contra he
    have hsmall : Small R (d + 1) (F.Factor i) := hd.devLE
    exact hs (hsmall.mono (Nat.succ_le_of_lt (Nat.lt_of_not_ge he)))
  · intro he hs
    exact hd.not_small (hs.mono he)

/-- There are at most as many surviving factors as total factors. -/
theorem topLength_le_length (e : ℕ) : F.topLength e ≤ F.length := by
  classical
  unfold topLength
  calc
    _ ≤ ∑ _ : Fin F.length, 1 := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
    _ = F.length := by simp

/-- An integer rank on the submodule lattice detects every non-small interval.
The bound counts precisely the critical factors at the common top dimension. -/
theorem exists_bounded_rank {e : ℕ} (F : CriticalFiltration R e M) :
    ∃ r : Submodule R M → ℕ, Monotone r ∧ (∀ p, r p ≤ F.topLength e) ∧
      ∀ p q, p ≤ q → r p = r q → Small R e (q ⧸ p.comap q.subtype) := by
  have hr := intervalRank_series F.toRelSeries
  have hw : seriesWeight e F.toRelSeries = F.topLength e := rfl
  rw [hw, F.head_eq_bot, F.last_eq_top] at hr
  obtain ⟨r, hm, hb, hs⟩ := hr
  let j : Submodule R M → Set.Icc (⊥ : Submodule R M) ⊤ := fun p => ⟨p, bot_le, le_top⟩
  refine ⟨r ∘ j, fun p q h => hm h, fun p => hb _, ?_⟩
  intro p q hpq he
  exact (orderSmall_interval_iff e hpq).mp (hs (j p) (j q) hpq he)

/-- Every finite portion of any ascending chain has at most `topLength`
non-small successive factors. Thus the bound is independent of the chain. -/
theorem non_small_chain_count_le {e : ℕ} (F : CriticalFiltration R e M)
    (c : ℕ → Submodule R M) (hc : Monotone c) (k : ℕ) :
    ((Finset.range k).filter (fun i =>
      ¬Small R e (c (i + 1) ⧸ (c i).comap (c (i + 1)).subtype))).card ≤ F.topLength e := by
  classical
  obtain ⟨r, hm, hb, hs⟩ := F.exists_bounded_rank
  have aux : ∀ k, ((Finset.range k).filter (fun i =>
      ¬Small R e (c (i + 1) ⧸ (c i).comap (c (i + 1)).subtype))).card ≤ r (c k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hle := hm (hc (Nat.le_succ k))
      by_cases hsmall : Small R e (c (k + 1) ⧸ (c k).comap (c (k + 1)).subtype)
      · simpa [Finset.range_add_one, Finset.filter_insert, hsmall, Finset.mem_filter] using ih.trans hle
      · have hlt : r (c k) < r (c (k + 1)) :=
          lt_of_le_of_ne hle (fun he => hsmall (hs _ _ (hc (Nat.le_succ k)) he))
        have hbound : ((Finset.range k).filter (fun i =>
            ¬Small R e (c (i + 1) ⧸ (c i).comap (c (i + 1)).subtype))).card + 1 ≤
            r (c (k + 1)) := by omega
        simpa [Finset.range_add_one, Finset.filter_insert, hsmall, Finset.mem_filter] using hbound
  exact (aux k).trans (hb _)

/-- In particular, a chain with every factor non-small has bounded length. -/
theorem non_small_chain_length_le {e : ℕ} (F : CriticalFiltration R e M)
    (c : ℕ → Submodule R M) (hc : Monotone c) (k : ℕ)
    (h : ∀ i < k, ¬Small R e (c (i + 1) ⧸ (c i).comap (c (i + 1)).subtype)) :
    k ≤ F.topLength e := by
  classical
  have he : (Finset.range k).filter (fun i =>
      ¬Small R e (c (i + 1) ⧸ (c i).comap (c (i + 1)).subtype)) = Finset.range k :=
    Finset.filter_eq_self.mpr (fun i hi => h i (Finset.mem_range.mp hi))
  simpa only [he, Finset.card_range] using F.non_small_chain_count_le c hc k


end CriticalFiltration

end Module
