module

public import AlgebraicAnalysis.RingTheory.Goldie.Basic
public import AlgebraicAnalysis.Module.TorsionEscape
public import AlgebraicAnalysis.Module.GermSchur

@[expose] public section

/-!
# Goldie torsion

A right module `M` over a ring `R` is *Goldie-torsion* (`IsGoldieTorsion R M`)
if every element of `M` is killed by a regular element of `R`. Over a domain
this is ordinary torsion. This file records the closure properties of the
class and, over a simple right Noetherian ring:

* `R / I` is Goldie-torsion when `I` contains a regular element
  (`isGoldieTorsion_quotient`);
* a finite-dimensional subspace of a Goldie-torsion bimodule has a common
  regular right annihilator
  (`IsGoldieTorsion.exists_common_regular_annihilator`);
* escape: for `g ≠ 0` and `b ≠ 0` (possibly singular), `g R b` is not contained
  in any finite-dimensional left subspace (`IsGoldieTorsion.exists_smul_mul_not_mem`),
  hence an injective finite-dimensional map stays injective after right
  multiplication by some `r b` (`IsGoldieTorsion.exists_injective_right_mul`);
* Goldie torsion passes from a critical module to its section module
  (`isGoldieTorsion_section`).

The linear-algebra steps are those of `AlgebraicAnalysis.TorsionEscape`; only
the torsion input changes, from the right Ore condition of a domain to Goldie's
theorem (`AlgebraicAnalysis.Goldie.exists_mem_nonZeroDivisors_finset`).
-/

namespace AlgebraicAnalysis.Goldie

open MulOpposite nonZeroDivisors
open AlgebraicAnalysis.TorsionEscape AlgebraicAnalysis.DenominatorTorsion

universe u v

/-- A right `R`-module `M` is Goldie-torsion if every element is killed by a
regular element of `R`. -/
def IsGoldieTorsion (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    Prop :=
  ∀ m : M, ∃ s ∈ R⁰, op s • m = 0

section Closure

variable {R : Type u} [Ring R]
variable {M N : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N]

theorem IsGoldieTorsion.of_injective (f : M →ₗ[Rᵐᵒᵖ] N) (hf : Function.Injective f)
    (hN : IsGoldieTorsion R N) : IsGoldieTorsion R M := fun m => by
  obtain ⟨s, hs, hsm⟩ := hN (f m)
  exact ⟨s, hs, hf (by rw [map_smul, hsm, map_zero])⟩

theorem IsGoldieTorsion.of_surjective (f : M →ₗ[Rᵐᵒᵖ] N) (hf : Function.Surjective f)
    (hM : IsGoldieTorsion R M) : IsGoldieTorsion R N := fun n => by
  obtain ⟨m, rfl⟩ := hf n
  obtain ⟨s, hs, hsm⟩ := hM m
  exact ⟨s, hs, by rw [← map_smul, hsm, map_zero]⟩

/-- Goldie torsion is ordinary torsion (regular elements are nonzero). -/
theorem IsGoldieTorsion.isTorsionRight [Nontrivial R] (hM : IsGoldieTorsion R M) :
    IsTorsionRight (R := R) (M := M) := fun m => by
  obtain ⟨s, hs, hsm⟩ := hM m
  exact ⟨s, nonZeroDivisors.ne_zero hs, hsm⟩

/-- Over a domain, ordinary torsion is Goldie torsion. -/
theorem isGoldieTorsion_of_isTorsionRight [IsDomain R]
    (hM : IsTorsionRight (R := R) (M := M)) : IsGoldieTorsion R M := fun m => by
  obtain ⟨s, hs, hsm⟩ := hM m
  exact ⟨s, mem_nonZeroDivisors_of_ne_zero hs, hsm⟩

/-- A quotient `R/I` with `I` containing a regular element is Goldie-torsion. -/
theorem isGoldieTorsion_quotient [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ∈ R⁰) :
    IsGoldieTorsion R (R ⧸ I) := fun z => by
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective I z
  obtain ⟨b, hb, hfb⟩ := exists_mul_mem_of_mem_nonZeroDivisors hsI hs f
  refine ⟨b, hb, ?_⟩
  rw [← map_smul]
  exact (Submodule.Quotient.mk_eq_zero I).mpr hfb

/-- If every `y ∈ I` has a regular `s` with `y s ∈ aR`, then `I / aR` (the
quotient of `I` by `aR ∩ I`) is Goldie-torsion. -/
theorem isGoldieTorsion_quotient_of_forall_exists_mul_mem {I : Submodule Rᵐᵒᵖ R} {a : R}
    (hIa : ∀ y ∈ I, ∃ s ∈ R⁰, y * s ∈ principalRightIdeal a) :
    IsGoldieTorsion R (↥I ⧸ (principalRightIdeal a).comap I.subtype) := by
  intro z
  obtain ⟨⟨m, hm⟩, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨s, hs, hms⟩ := hIa m hm
  refine ⟨s, hs, ?_⟩
  rw [← map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hms

/-- In a simple right Noetherian ring every right ideal `I` contains an
element `a` with `I / aR` Goldie-torsion. -/
theorem exists_mem_isGoldieTorsion_quotient [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    (I : Submodule Rᵐᵒᵖ R) :
    ∃ a ∈ I, IsGoldieTorsion R (↥I ⧸ (principalRightIdeal a).comap I.subtype) := by
  obtain ⟨a, haI, hIa⟩ := exists_mem_forall_exists_mul_mem I
  exact ⟨a, haI, isGoldieTorsion_quotient_of_forall_exists_mul_mem hIa⟩

end Closure

section Escape

variable {R E W : Type*} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] [DivisionRing E]
variable [AddCommGroup W] [Module Rᵐᵒᵖ W] [Module E W]
variable [SMulCommClass Rᵐᵒᵖ E W]

/-- A finite-dimensional subspace of a Goldie-torsion bimodule has a common
regular right annihilator. -/
theorem IsGoldieTorsion.exists_common_regular_annihilator (hW : IsGoldieTorsion R W)
    (Y : Submodule E W) [Module.Finite E Y] :
    ∃ c ∈ R⁰, ∀ y ∈ Y, op c • y = 0 := by
  classical
  let B := Module.finBasis E Y
  obtain ⟨c, hc, hcB⟩ := exists_mem_nonZeroDivisors_finset Finset.univ
    (fun i => rightAnnihilator (R := R) (B i : W))
    (fun i _ => by
      obtain ⟨r, hr, hri⟩ := hW (B i : W)
      exact ⟨r, hri, hr⟩)
  refine ⟨c, hc, ?_⟩
  intro y hy
  have heq := congrArg (fun z : Y => (z : W)) (B.sum_repr ⟨y, hy⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at heq
  rw [← heq, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [smul_comm, show op c • (B i : W) = 0 from hcB i (Finset.mem_univ i), smul_zero]

/-- **Escape.** In a Goldie-torsion bimodule over a simple right Noetherian
ring, for `g ≠ 0` and `b ≠ 0` (possibly singular), `g R b` is not contained in
any finite-dimensional left subspace. -/
theorem IsGoldieTorsion.exists_smul_mul_not_mem (hW : IsGoldieTorsion R W)
    {g : W} (hg : g ≠ 0) {b : R} (hb : b ≠ 0)
    (Y : Submodule E W) [Module.Finite E Y] :
    ∃ r : R, op (r * b) • g ∉ Y := by
  classical
  by_contra! h
  obtain ⟨c, hc, hcY⟩ := hW.exists_common_regular_annihilator Y
  have hbc : b * c ∈ cyclicAnnihilator g := by
    simp only [cyclicAnnihilator, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq]
    intro r
    rw [← mul_assoc, op_mul, mul_smul]
    exact hcY _ (h r)
  have hbc0 : b * c ≠ 0 := fun h0 => hb (hc.2 b h0)
  have h1 := IsSimpleRing.one_mem_of_ne_zero_mem (cyclicAnnihilator g) hbc0 hbc
  have hzero := h1 1
  exact hg (by simpa using hzero)

variable {k D : Type*} [Field k] [Infinite k]
variable [AddCommGroup D] [Module E D] [Module.Finite E D]

/-- A finite-dimensional injective map into a Goldie-torsion bimodule stays
injective after right multiplication by `r b` for some `r`, for any `b ≠ 0`. -/
theorem IsGoldieTorsion.exists_injective_right_mul (hW : IsGoldieTorsion R W)
    (σ : k →+* R) (κ : k →+* E) (hκ : ∀ c a, κ c * a = a * κ c)
    (hscalar : ∀ c (w : W), op (σ c) • w = κ c • w)
    (P : D →ₗ[E] W) (hP : Function.Injective P) {b : R} (hb : b ≠ 0) :
    ∃ r : R, Function.Injective ((rightMulLinear (E := E) (r * b)).comp P) := by
  apply exists_injective_of_escape σ κ hκ
    (fun r => (rightMulLinear (E := E) (r * b)).comp P)
  · intro r s c d
    change op ((r + σ c * s) * b) • P d =
      op (r * b) • P d + κ c • (op (s * b) • P d)
    rw [add_mul, op_add, add_smul, mul_assoc]
    congr 1
    rw [op_mul, mul_smul, hscalar, smul_comm]
  · intro d hd Y hY
    let := hY
    exact hW.exists_smul_mul_not_mem
      (fun h => hd (hP (h.trans (map_zero P).symm))) hb Y

end Escape

section Section

open Module Module.Germ

variable {R : Type u} [Ring R] [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] {e : ℕ}
variable {C : Type v} [AddCommGroup C] [Module Rᵐᵒᵖ C] [IsNoetherian Rᵐᵒᵖ C]

/-- Goldie torsion passes from a critical module to its section module: the
annihilator of a section is essential, hence contains a regular element
(Goldie). -/
theorem isGoldieTorsion_section (hC : Critical Rᵐᵒᵖ e C) (ht : IsGoldieTorsion R C) :
    IsGoldieTorsion R (Section R e C) := by
  intro w
  have hess : IsEssential (rightAnnihilator (R := R) w) := by
    intro y hy
    by_cases hyw : op y • w = 0
    · refine ⟨1, by rwa [mul_one], ?_⟩
      change op (y * 1) • w = 0
      rwa [mul_one]
    obtain ⟨i, c, hc, he⟩ := Section.exists_smul_eq_ofElement hC (op y • w) hyw
    rw [Section.right_action_assoc] at he
    obtain ⟨s, hs, hsc⟩ := ht c
    have hyi : y * i ≠ 0 := by
      intro h0
      rw [h0, op_zero, zero_smul] at he
      exact hc (Section.ofElement_injective hC (he.symm.trans (map_zero _).symm))
    refine ⟨i * s, fun h0 => hyi (hs.2 _ (by rwa [← mul_assoc] at h0)), ?_⟩
    change op (y * (i * s)) • w = 0
    rw [← mul_assoc, ← Section.right_action_assoc, he, ← map_smul, hsc, map_zero]
  obtain ⟨s, hsw, hs⟩ := exists_mem_nonZeroDivisors_of_isEssential hess
  exact ⟨s, hs, hsw⟩

end Section

end AlgebraicAnalysis.Goldie
