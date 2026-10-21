module
public import AlgebraicAnalysis.Order.Deviation
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality

@[expose] public section

/-!
# Finite deviation of modules

The scalar ring is arbitrary; right modules are obtained by using `Rᵐᵒᵖ`.
`Module.Small R 0 M` means that `M` is zero, whereas `Small R (e+1) M`
means deviation at most `e`. No dimension is assigned to modules without a
finite bound. The exact-sequence maximum is expressed as an equivalence of
bounds, so no existence of a dimension is implicit.
-/

universe u v w

open scoped DirectSum

namespace Module

/-- The submodule lattice has finite deviation at most `n`. -/
def DevLE (R : Type u) (n : ℕ) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] : Prop := Order.DevLE n (Submodule R M)

/-- The finite strict stratum: zero is the zero module; stratum `e+1`
consists of modules with deviation at most `e`. -/
def Small (R : Type u) (e : ℕ) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] : Prop :=
  match e with
  | 0 => Subsingleton M
  | e + 1 => DevLE R e M

variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

@[simp] theorem small_zero_iff : Small R 0 M ↔ Subsingleton M := Iff.rfl
@[simp] theorem small_succ_iff (e : ℕ) : Small R (e + 1) M ↔ DevLE R e M := Iff.rfl

/-- Deviation zero agrees with Mathlib's Artinian condition. -/
theorem devLE_zero_iff_isArtinian : DevLE R 0 M ↔ IsArtinian R M := by
  rw [← monotone_stabilizes_iff_artinian]
  constructor
  · intro h c
    obtain ⟨n, hn⟩ := h c c.monotone
    exact ⟨n, fun m hm => (hn m hm).symm⟩
  · intro h c hc
    obtain ⟨n, hn⟩ := h ⟨c, hc⟩
    exact ⟨n, fun m hm => (hn m hm).symm⟩

theorem DevLE.mono {n m : ℕ} (h : DevLE R n M) (hnm : n ≤ m) : DevLE R m M :=
  Order.DevLE.mono h hnm

theorem devLE_of_subsingleton (n : ℕ) [Subsingleton M] : DevLE R n M :=
  Order.devLE_of_subsingleton n

theorem small_of_subsingleton (e : ℕ) [Subsingleton M] : Small R e M := by
  cases e with
  | zero => exact (inferInstance : Subsingleton M)
  | succ n => exact devLE_of_subsingleton n

theorem Small.mono {e f : ℕ} (h : Small R e M) (hef : e ≤ f) : Small R f M := by
  cases e with
  | zero =>
    have : Subsingleton M := h
    exact small_of_subsingleton f
  | succ e =>
    cases f with
    | zero => omega
    | succ f => exact DevLE.mono h (Nat.le_of_succ_le_succ hef)

theorem devLE_linearEquiv_iff (n : ℕ) (e : M ≃ₗ[R] N) :
    DevLE R n M ↔ DevLE R n N :=
  Order.devLE_orderIso_iff n (Submodule.orderIsoMapComap e)

theorem small_linearEquiv_iff (e : ℕ) (f : M ≃ₗ[R] N) :
    Small R e M ↔ Small R e N := by
  cases e with
  | zero =>
    constructor
    · intro h
      exact ⟨fun x y => f.symm.injective (h.elim _ _)⟩
    · intro h
      exact ⟨fun x y => f.injective (h.elim _ _)⟩
  | succ n => exact devLE_linearEquiv_iff n f

theorem DevLE.of_injective {n : ℕ} (h : DevLE R n N) (f : M →ₗ[R] N)
    (hf : Function.Injective f) : DevLE R n M :=
  Order.DevLE.of_strictMono h (Submodule.map_strictMono_of_injective hf)

theorem DevLE.of_surjective {n : ℕ} (h : DevLE R n M) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : DevLE R n N :=
  Order.DevLE.of_strictMono h (Submodule.comap_strictMono_of_surjective hf)

theorem DevLE.submodule {n : ℕ} (h : DevLE R n M) (p : Submodule R M) : DevLE R n p :=
  h.of_injective p.subtype Subtype.val_injective

theorem DevLE.quotient {n : ℕ} (h : DevLE R n M) (p : Submodule R M) :
    DevLE R n (M ⧸ p) :=
  h.of_surjective p.mkQ (Submodule.mkQ_surjective p)

theorem Small.of_injective {e : ℕ} (h : Small R e N) (f : M →ₗ[R] N)
    (hf : Function.Injective f) : Small R e M := by
  cases e with
  | zero => exact ⟨fun x y => hf (h.elim _ _)⟩
  | succ n => exact DevLE.of_injective h f hf

theorem Small.of_surjective {e : ℕ} (h : Small R e M) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : Small R e N := by
  cases e with
  | zero =>
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    exact congrArg f (h.elim a b)
  | succ n => exact DevLE.of_surjective h f hf

theorem Small.submodule {e : ℕ} (h : Small R e M) (p : Submodule R M) : Small R e p :=
  h.of_injective p.subtype Subtype.val_injective

theorem Small.quotient {e : ℕ} (h : Small R e M) (p : Submodule R M) : Small R e (M ⧸ p) :=
  h.of_surjective p.mkQ (Submodule.mkQ_surjective p)

/-- The finite-deviation maximum formula for a submodule and its quotient. -/
theorem devLE_iff_submodule_quotient (n : ℕ) (p : Submodule R M) :
    DevLE R n M ↔ DevLE R n p ∧ DevLE R n (M ⧸ p) := by
  refine ⟨fun h => ⟨h.submodule p, h.quotient p⟩, fun h => ?_⟩
  exact (Order.DevLE.prod h.1 h.2).of_strictMono (Submodule.strictMono_comap_prod_map p)

/-- Zero is kept distinct from Artinian modules in the exact maximum formula. -/
theorem small_iff_submodule_quotient (e : ℕ) (p : Submodule R M) :
    Small R e M ↔ Small R e p ∧ Small R e (M ⧸ p) := by
  cases e with
  | zero =>
    refine ⟨fun h => ⟨h.submodule p, h.quotient p⟩, fun h => ?_⟩
    have hp : Subsingleton p := h.1
    have hq : Subsingleton (M ⧸ p) := h.2
    apply subsingleton_of_forall_eq 0
    intro x
    have hx : x ∈ p := (Submodule.Quotient.mk_eq_zero p).mp (Subsingleton.elim _ _)
    exact congrArg Subtype.val (show (⟨x, hx⟩ : p) = 0 from Subsingleton.elim _ _)
  | succ n => exact devLE_iff_submodule_quotient n p

/-- Extension closure, without finiteness or Noetherian hypotheses. -/
theorem DevLE.of_submodule_quotient {n : ℕ} (p : Submodule R M)
    (hp : DevLE R n p) (hq : DevLE R n (M ⧸ p)) : DevLE R n M :=
  (devLE_iff_submodule_quotient n p).mpr ⟨hp, hq⟩

theorem Small.of_submodule_quotient {e : ℕ} (p : Submodule R M)
    (hp : Small R e p) (hq : Small R e (M ⧸ p)) : Small R e M :=
  (small_iff_submodule_quotient e p).mpr ⟨hp, hq⟩

/-- The maximum formula for an arbitrary short exact sequence of modules. -/
theorem devLE_iff_of_exact {P : Type*} [AddCommGroup P] [Module R P]
    (n : ℕ) (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    DevLE R n M ↔ DevLE R n N ∧ DevLE R n P := by
  have hek : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp hfg).symm
  let e : N ≃ₗ[R] LinearMap.ker g :=
    (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hek)
  rw [devLE_iff_submodule_quotient n (LinearMap.ker g),
    ← devLE_linearEquiv_iff n e,
    devLE_linearEquiv_iff n (g.quotKerEquivOfSurjective hg)]

theorem small_iff_of_exact {P : Type*} [AddCommGroup P] [Module R P]
    (e : ℕ) (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Small R e M ↔ Small R e N ∧ Small R e P := by
  have hek : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp hfg).symm
  let k : N ≃ₗ[R] LinearMap.ker g :=
    (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hek)
  rw [small_iff_submodule_quotient e (LinearMap.ker g),
    ← small_linearEquiv_iff e k,
    small_linearEquiv_iff e (g.quotKerEquivOfSurjective hg)]

/-- The intersection/projection map for the split exact sequence of a product. -/
private theorem strictMono_prod_submodules : StrictMono
    (fun p : Submodule R (M × N) =>
      (p.comap (LinearMap.inl R M N), p.map (LinearMap.snd R M N))) := by
  intro p q hpq
  refine lt_of_le_of_ne ⟨Submodule.comap_mono hpq.le, Submodule.map_mono hpq.le⟩ ?_
  intro he
  have he₁ : p.comap (LinearMap.inl R M N) = q.comap (LinearMap.inl R M N) :=
    congrArg Prod.fst he
  have he₂ : p.map (LinearMap.snd R M N) = q.map (LinearMap.snd R M N) :=
    congrArg Prod.snd he
  apply hpq.ne
  apply le_antisymm hpq.le
  intro x hx
  obtain ⟨y, hy, hyx⟩ := (show x.2 ∈ p.map (LinearMap.snd R M N) from
    he₂.symm ▸ Submodule.mem_map_of_mem hx)
  change y.2 = x.2 at hyx
  have hd : (x.1 - y.1, (0 : N)) ∈ q := by
    have := q.sub_mem hx (hpq.le hy)
    simpa [Prod.sub_def, hyx] using this
  have hd' : (x.1 - y.1, (0 : N)) ∈ p := by
    have : x.1 - y.1 ∈ p.comap (LinearMap.inl R M N) :=
      he₁.symm ▸ hd
    exact this
  have := p.add_mem hd' hy
  simpa [Prod.add_def, hyx] using this

theorem DevLE.prod {n : ℕ} (hM : DevLE R n M) (hN : DevLE R n N) :
    DevLE R n (M × N) :=
  (Order.DevLE.prod hM hN).of_strictMono strictMono_prod_submodules

theorem Small.prod {e : ℕ} (hM : Small R e M) (hN : Small R e N) :
    Small R e (M × N) := by
  cases e with
  | zero => exact ⟨fun x y => Prod.ext (hM.elim _ _) (hN.elim _ _)⟩
  | succ n => exact DevLE.prod hM hN

/-- Finite products (equivalently finite direct sums) preserve a bound. -/
theorem DevLE.pi {ι : Type w} [Finite ι] {P : ι → Type v}
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] {n : ℕ}
    (h : ∀ i, DevLE R n (P i)) : DevLE R n (∀ i, P i) := by
  apply Module.pi_induction' R
    (fun X _ _ => DevLE R n X) (fun X _ _ => DevLE R n X)
    (fun f h => (devLE_linearEquiv_iff n f).mp h)
    (fun f h => (devLE_linearEquiv_iff n f).mp h)
    (devLE_of_subsingleton n) (fun h h' => h.prod h') P h

theorem Small.pi {ι : Type w} [Finite ι] {P : ι → Type v}
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] {e : ℕ}
    (h : ∀ i, Small R e (P i)) : Small R e (∀ i, P i) := by
  cases e with
  | zero => exact ⟨fun f g => funext fun i => (h i).elim _ _⟩
  | succ n => exact DevLE.pi h

/-- Finite direct sums preserve a deviation bound. No infinite-sum closure is asserted. -/
theorem DevLE.directSum {ι : Type w} [Finite ι] {P : ι → Type v}
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] {n : ℕ}
    (h : ∀ i, DevLE R n (P i)) : DevLE R n (⨁ i, P i) := by
  classical
  let := Fintype.ofFinite ι
  exact (devLE_linearEquiv_iff n (DirectSum.linearEquivFunOnFintype R ι P)).mpr
    (DevLE.pi h)

theorem Small.directSum {ι : Type w} [Finite ι] {P : ι → Type v}
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] {e : ℕ}
    (h : ∀ i, Small R e (P i)) : Small R e (⨁ i, P i) := by
  classical
  let := Fintype.ofFinite ι
  exact (small_linearEquiv_iff e (DirectSum.linearEquivFunOnFintype R ι P)).mpr
    (Small.pi h)

/-- A bound for the regular module bounds every finitely generated module. -/
theorem DevLE.of_finite {n : ℕ} (h : DevLE R n R) [Module.Finite R M] : DevLE R n M := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  exact (DevLE.pi (P := fun _ : Fin k => R) fun _ => h).of_surjective f hf

end Module

namespace Submodule

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The interval `[B,A]` is the lattice of submodules of `A/B`, where the
denominator is pulled back along the inclusion of `A` in the ambient module. -/
def quotientIntervalOrderIso (B A : Submodule R M) (hBA : B ≤ A) :
    Submodule R (A ⧸ B.comap A.subtype) ≃o Set.Icc B A where
  toFun C := ⟨(C.comap (B.comap A.subtype).mkQ).map A.subtype,
    by
      have h := Submodule.map_mono (le_comap_mkQ (B.comap A.subtype) C)
        (f := A.subtype)
      simpa only [map_comap_subtype, inf_eq_right.mpr hBA] using h,
    map_subtype_le A _⟩
  invFun U := (U.val.comap A.subtype).map (B.comap A.subtype).mkQ
  left_inv C := by
    change (((C.comap (B.comap A.subtype).mkQ).map A.subtype).comap A.subtype).map
      (B.comap A.subtype).mkQ = C
    rw [comap_map_eq_of_injective (f := A.subtype) Subtype.val_injective]
    exact map_comap_eq_of_surjective (Submodule.mkQ_surjective _) C
  right_inv U := by
    apply Subtype.ext
    dsimp
    rw [comap_map_mkQ, sup_eq_right.mpr (comap_mono U.property.1),
      map_comap_subtype, inf_eq_right.mpr U.property.2]
  map_rel_iff' := by
    intro C D
    change (C.comap _).map A.subtype ≤ (D.comap _).map A.subtype ↔ C ≤ D
    rw [map_le_map_iff_of_injective Subtype.val_injective,
      comap_le_comap_iff_of_surjective (Submodule.mkQ_surjective _)]

/-- Successive lattice intervals and quotient-module deviation agree. -/
theorem devLE_interval_iff (n : ℕ) (B A : Submodule R M) (hBA : B ≤ A) :
    Order.DevLE n (Set.Icc B A) ↔ Module.DevLE R n (A ⧸ B.comap A.subtype) :=
  (Order.devLE_orderIso_iff n (quotientIntervalOrderIso B A hBA)).symm

end Submodule

namespace Module

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The successor bound in terms of successive quotient modules. -/
theorem devLE_succ_iff (n : ℕ) : DevLE R (n + 1) M ↔
    ∀ c : ℕ → Submodule R M, Antitone c → ∃ N, ∀ i, N ≤ i →
      DevLE R n (c i ⧸ (c (i + 1)).comap (c i).subtype) := by
  unfold DevLE
  rw [Order.devLE_succ_iff]
  constructor <;> intro h c hc <;> obtain ⟨N, hN⟩ := h c hc
  · exact ⟨N, fun i hi => (Submodule.devLE_interval_iff n _ _ (hc (Nat.le_succ i))).mp
      (hN i hi)⟩
  · exact ⟨N, fun i hi => (Submodule.devLE_interval_iff n _ _ (hc (Nat.le_succ i))).mpr
      (hN i hi)⟩

end Module
