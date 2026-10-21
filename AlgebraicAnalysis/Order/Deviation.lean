module
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Hom.Basic

@[expose] public section

/-!
# Finite deviation of partially ordered sets

`Order.DevLE n α` is the finite Gabriel–Rentschler deviation bound. At zero it
is the descending chain condition; at a successor, successive closed intervals
of every descending chain eventually have the preceding bound. It is not the
supremum of lengths of finite strict chains.

The definition needs only a partial order. Strictly monotone maps pull bounds
back, and finite products preserve bounds. These two facts also apply to the
intersection/projection map for submodule lattices.
-/

universe u v

namespace Order

/-- Finite deviation at most `n`. Zero means that descending chains stabilize.
The trivial order has every bound, including zero. -/
def DevLE : (n : ℕ) → (α : Type u) → [PartialOrder α] → Prop
  | 0, α, _ => ∀ c : ℕ → α, Antitone c → ∃ N, ∀ i, N ≤ i → c i = c N
  | n + 1, α, _ => ∀ c : ℕ → α, Antitone c →
      ∃ N, ∀ i, N ≤ i → DevLE n (Set.Icc (c (i + 1)) (c i))

variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]

theorem devLE_zero_iff : DevLE 0 α ↔
    ∀ c : ℕ → α, Antitone c → ∃ N, ∀ i, N ≤ i → c i = c N := Iff.rfl

theorem devLE_succ_iff (n : ℕ) : DevLE (n + 1) α ↔
    ∀ c : ℕ → α, Antitone c →
      ∃ N, ∀ i, N ≤ i → DevLE n (Set.Icc (c (i + 1)) (c i)) := Iff.rfl

/-- A strictly monotone map reflects finite deviation bounds. Injectivity on
incomparable pairs is unnecessary. -/
theorem DevLE.of_strictMono {n : ℕ} (h : DevLE n β) {f : α → β}
    (hf : StrictMono f) : DevLE n α := by
  induction n generalizing α β with
  | zero =>
    intro c hc
    obtain ⟨N, hN⟩ := h (f ∘ c) (hf.monotone.comp_antitone hc)
    refine ⟨N, fun i hi => ?_⟩
    by_contra he
    have hlt : c i < c N := lt_of_le_of_ne (hc hi) he
    exact (ne_of_lt (hf hlt)) (hN i hi)
  | succ n ih =>
    intro c hc
    obtain ⟨N, hN⟩ := h (f ∘ c) (hf.monotone.comp_antitone hc)
    refine ⟨N, fun i hi => ?_⟩
    let g : Set.Icc (c (i + 1)) (c i) → Set.Icc (f (c (i + 1))) (f (c i)) :=
      fun x => ⟨f x, hf.monotone x.property.1, hf.monotone x.property.2⟩
    exact ih (hN i hi) (f := g) (fun _ _ hxy => hf hxy)

/-- Finite deviation is invariant under order isomorphisms. -/
theorem devLE_orderIso_iff (n : ℕ) (e : α ≃o β) : DevLE n α ↔ DevLE n β :=
  ⟨fun h => h.of_strictMono e.symm.strictMono, fun h => h.of_strictMono e.strictMono⟩

/-- Every interval inherits a deviation bound. -/
theorem DevLE.interval {n : ℕ} (h : DevLE n α) (a b : α) : DevLE n (Set.Icc a b) :=
  h.of_strictMono (f := Subtype.val) (fun _ _ hxy => hxy)

theorem devLE_of_subsingleton (n : ℕ) [Subsingleton α] : DevLE n α := by
  induction n generalizing α with
  | zero => exact fun c _ => ⟨0, fun _ _ => Subsingleton.elim _ _⟩
  | succ n ih => exact fun c _ => ⟨0, fun i _ => ih⟩

/-- Bounds increase monotonically with the finite index. -/
theorem DevLE.succ {n : ℕ} (h : DevLE n α) : DevLE (n + 1) α := by
  induction n generalizing α with
  | zero =>
    intro c hc
    obtain ⟨N, hN⟩ := h c hc
    refine ⟨N, fun i hi => ?_⟩
    have he : c (i + 1) = c i := (hN (i + 1) (Nat.le_trans hi (Nat.le_succ i))).trans
      (hN i hi).symm
    have : Subsingleton (Set.Icc (c (i + 1)) (c i)) := by
      rw [he]
      infer_instance
    exact devLE_of_subsingleton 0
  | succ n ih =>
    intro c hc
    obtain ⟨N, hN⟩ := h c hc
    exact ⟨N, fun i hi => ih (hN i hi)⟩

theorem DevLE.mono {n m : ℕ} (h : DevLE n α) (hnm : n ≤ m) : DevLE m α := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact ih.succ

/-- Products preserve finite deviation bounds. -/
theorem DevLE.prod {n : ℕ} (hα : DevLE n α) (hβ : DevLE n β) :
    DevLE n (α × β) := by
  induction n generalizing α β with
  | zero =>
    intro c hc
    obtain ⟨N, hN⟩ := hα (fun i => (c i).1) (fun _ _ hij => (hc hij).1)
    obtain ⟨M, hM⟩ := hβ (fun i => (c i).2) (fun _ _ hij => (hc hij).2)
    refine ⟨max N M, fun i hi => Prod.ext ?_ ?_⟩
    · exact (hN i (le_trans (le_max_left _ _) hi)).trans
        (hN _ (le_max_left _ _)).symm
    · exact (hM i (le_trans (le_max_right _ _) hi)).trans
        (hM _ (le_max_right _ _)).symm
  | succ n ih =>
    intro c hc
    obtain ⟨N, hN⟩ := hα (fun i => (c i).1) (fun _ _ hij => (hc hij).1)
    obtain ⟨M, hM⟩ := hβ (fun i => (c i).2) (fun _ _ hij => (hc hij).2)
    refine ⟨max N M, fun i hi => ?_⟩
    have hp := ih (hN i (le_trans (le_max_left _ _) hi))
      (hM i (le_trans (le_max_right _ _) hi))
    let f : Set.Icc (c (i + 1)) (c i) →
        Set.Icc ((c (i + 1)).1) ((c i).1) × Set.Icc ((c (i + 1)).2) ((c i).2) :=
      fun x => (⟨x.val.1, x.property.1.1, x.property.2.1⟩,
        ⟨x.val.2, x.property.1.2, x.property.2.2⟩)
    apply hp.of_strictMono (f := f)
    intro x y hxy
    exact hxy

end Order
