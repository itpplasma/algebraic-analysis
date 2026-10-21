module
public import AlgebraicAnalysis.Module.DenominatorTorsion

@[expose] public section

/-!
# A right-ideal colon bound for a Serre predicate

The predicate is explicit and carries no dimension or localization assumptions.
All products below retain their right-module order. In particular the relation
`f * d * L = d * C` is an input, not a commutativity assumption.
-/

namespace AlgebraicAnalysis.ColonSupport

open DenominatorTorsion

universe u
variable {R : Type u} [Ring R]

/-- An isomorphism-invariant class closed under submodules, quotients and
extensions, expressed directly using linear maps and exact sequences. -/
structure IsSerreClosed
    (P : (M : Type u) → [AddCommGroup M] → [Module Rᵐᵒᵖ M] → Prop) : Prop where
  of_injective : ∀ {M N : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [AddCommGroup N] [Module Rᵐᵒᵖ N] (i : M →ₗ[Rᵐᵒᵖ] N),
    Function.Injective i → P N → P M
  of_surjective : ∀ {M N : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [AddCommGroup N] [Module Rᵐᵒᵖ N] (p : M →ₗ[Rᵐᵒᵖ] N),
    Function.Surjective p → P M → P N
  of_exact : ∀ {A B C : Type u} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup B] [Module Rᵐᵒᵖ B] [AddCommGroup C] [Module Rᵐᵒᵖ C]
    (i : A →ₗ[Rᵐᵒᵖ] B) (p : B →ₗ[Rᵐᵒᵖ] C),
    Function.Injective i → Function.Surjective p → Function.Exact i p →
    P A → P C → P B

/-- `D = dR`. -/
abbrev anchor (d : R) := principalRightIdeal d

/-- `K = {s | g*d*s ∈ dR}`. -/
def colon (d g : R) : Submodule Rᵐᵒᵖ R :=
  (anchor d).comap (leftMulLinear (g * d))

/-- `I = dR + f*d*R`. -/
def firstIdeal (d f : R) : Submodule Rᵐᵒᵖ R :=
  anchor d ⊔ principalRightIdeal (f * d)

/-- `Q = dR + g*d*L*R`, with the original anchor `d`. -/
def secondIdeal (d g L : R) : Submodule Rᵐᵒᵖ R :=
  anchor d ⊔ principalRightIdeal (g * d * L)

/-- `J = dR + f*d*K`. -/
def refinedIdeal (d f g : R) : Submodule Rᵐᵒᵖ R :=
  anchor d ⊔ (colon d g).map (leftMulLinear (f * d))

/-- The common source ideal `K + LR`. -/
def sourceIdeal (d g L : R) : Submodule Rᵐᵒᵖ R :=
  colon d g ⊔ principalRightIdeal L

/-- The refined ideal is contained in the original two-generator ideal. -/
theorem refinedIdeal_le_firstIdeal (d f g : R) :
    refinedIdeal d f g ≤ firstIdeal d f := by
  apply sup_le le_sup_left
  rintro x ⟨s, _, rfl⟩
  exact Submodule.mem_sup_right ⟨s, rfl⟩

/-- Adding a central multiple of `g` to `f` still contains the refined ideal. -/
theorem refinedIdeal_le_pencil (d f g lam : R)
    (hlam : ∀ x : R, lam * x = x * lam) :
    refinedIdeal d f g ≤ firstIdeal d (f + lam * g) := by
  apply sup_le le_sup_left
  rintro x ⟨s, hs, rfl⟩
  obtain ⟨c, hc⟩ := hs
  change d * c = g * d * s at hc
  have heq : f * d * s = d * (-(lam * c)) + (f + lam * g) * d * s := by
    calc
      f * d * s = -(lam * (g * d * s)) + (f * d * s + lam * (g * d * s)) := by abel
      _ = d * (-(lam * c)) + (f + lam * g) * d * s := by
        have hneg : d * (-(lam * c)) = -(lam * (g * d * s)) := by
          rw [mul_neg, ← mul_assoc, ← hlam d, mul_assoc, hc]
        rw [hneg]
        noncomm_ring
  rw [show leftMulLinear (f * d) s = f * d * s from rfl, heq]
  exact Submodule.add_mem_sup ⟨-(lam * c), rfl⟩ ⟨s, rfl⟩

/-- The preimage of `Q` under multiplication by `gd` is exactly `K + LR`. -/
theorem comap_secondIdeal (d g L : R) :
    (secondIdeal d g L).comap (leftMulLinear (g * d)) = sourceIdeal d g L := by
  ext s
  constructor
  · intro hs
    obtain ⟨u, ⟨x, hx⟩, v, ⟨y, hy⟩, huv⟩ := Submodule.mem_sup.mp hs
    change d * x = u at hx
    change g * d * L * y = v at hy
    change u + v = g * d * s at huv
    have hk : s - L * y ∈ colon d g := by
      refine ⟨x, ?_⟩
      change d * x = g * d * (s - L * y)
      rw [mul_sub, ← mul_assoc, hx, hy]
      exact eq_sub_of_add_eq huv
    exact Submodule.mem_sup.mpr ⟨s - L * y, hk, L * y, ⟨y, rfl⟩, sub_add_cancel _ _⟩
  · intro hs
    obtain ⟨k, hk, l, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hs
    change g * d * (k + L * y) ∈ secondIdeal d g L
    rw [mul_add, ← mul_assoc]
    exact Submodule.add_mem_sup hk ⟨y, rfl⟩

/-- `s ↦ gd*s + Q`, factored through `R/(K+LR)`. -/
def colonEmbedding (d g L : R) :
    (R ⧸ sourceIdeal d g L) →ₗ[Rᵐᵒᵖ] (R ⧸ secondIdeal d g L) :=
  (sourceIdeal d g L).mapQ (secondIdeal d g L) (leftMulLinear (g * d))
    (comap_secondIdeal d g L).ge

@[simp] theorem colonEmbedding_mk (d g L s : R) :
    colonEmbedding d g L ((sourceIdeal d g L).mkQ s) =
      (secondIdeal d g L).mkQ (g * d * s) := rfl

/-- The first colon map is an embedding, including when `gd = 0`. -/
theorem colonEmbedding_injective (d g L : R) :
    Function.Injective (colonEmbedding d g L) := by
  rw [← LinearMap.ker_eq_bot, colonEmbedding, Submodule.ker_mapQ,
    comap_secondIdeal, Submodule.mkQ_map_self]

/-- The quotient `I/J`, formed inside the right ideal `I`. -/
abbrev idealQuotient (d f g : R) :=
  firstIdeal d f ⧸ (refinedIdeal d f g).comap (firstIdeal d f).subtype

/-- Left multiplication by `fd`, with codomain restricted to `I`. -/
def idealNumerator (d f : R) : R →ₗ[Rᵐᵒᵖ] firstIdeal d f :=
  (leftMulLinear (f * d)).codRestrict _ (fun s => Submodule.mem_sup_right ⟨s, rfl⟩)

/-- The relation `fdL = dC` kills `K+LR` modulo `J`. -/
theorem sourceIdeal_le_ker (d f g L C : R) (h : f * d * L = d * C) :
    sourceIdeal d g L ≤ LinearMap.ker
      (((refinedIdeal d f g).comap (firstIdeal d f).subtype).mkQ.comp (idealNumerator d f)) := by
  intro s hs
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change f * d * s ∈ refinedIdeal d f g
  obtain ⟨k, hk, l, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hs
  rw [mul_add]
  apply (refinedIdeal d f g).add_mem
  · exact Submodule.mem_sup_right ⟨k, hk, rfl⟩
  · apply Submodule.mem_sup_left
    exact ⟨C * y, by change d * (C * y) = f * d * (L * y); rw [← mul_assoc, ← h, mul_assoc]⟩

/-- `s ↦ fd*s + J`, factored through the same source as `colonEmbedding`. -/
def colonSurjection (d f g L C : R) (h : f * d * L = d * C) :
    (R ⧸ sourceIdeal d g L) →ₗ[Rᵐᵒᵖ] idealQuotient d f g :=
  (sourceIdeal d g L).liftQ
    (((refinedIdeal d f g).comap (firstIdeal d f).subtype).mkQ.comp (idealNumerator d f))
    (sourceIdeal_le_ker d f g L C h)

@[simp] theorem colonSurjection_mk (d f g L C s : R) (h : f * d * L = d * C) :
    colonSurjection d f g L C h ((sourceIdeal d g L).mkQ s) =
      ((refinedIdeal d f g).comap (firstIdeal d f).subtype).mkQ (idealNumerator d f s) := rfl

/-- The second colon map covers `I/J` because the other summand `D` is killed. -/
theorem colonSurjection_surjective (d f g L C : R) (h : f * d * L = d * C) :
    Function.Surjective (colonSurjection d f g L C h) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    obtain ⟨u, hu, v, ⟨s, rfl⟩, huv⟩ := Submodule.mem_sup.mp x.property
    refine ⟨(sourceIdeal d g L).mkQ s, ?_⟩
    rw [colonSurjection_mk, Submodule.mkQ_apply, Submodule.Quotient.eq]
    change f * d * s - x.val ∈ refinedIdeal d f g
    have hx : x.val = u + f * d * s := huv.symm
    rw [hx, show f * d * s - (u + f * d * s) = -u by abel]
    exact (refinedIdeal d f g).neg_mem (Submodule.mem_sup_left hu)

/-- The usual inclusion `I/J → R/J`. -/
def quotientInclusion (d f g : R) :
    idealQuotient d f g →ₗ[Rᵐᵒᵖ] (R ⧸ refinedIdeal d f g) :=
  ((refinedIdeal d f g).comap (firstIdeal d f).subtype).mapQ
    (refinedIdeal d f g) (firstIdeal d f).subtype le_rfl

/-- The inclusion of the subquotient has zero kernel. -/
theorem quotientInclusion_injective (d f g : R) :
    Function.Injective (quotientInclusion d f g) := by
  rw [← LinearMap.ker_eq_bot, quotientInclusion, Submodule.ker_mapQ,
    Submodule.mkQ_map_self]

/-- `I/J → R/J → R/I` is exact. -/
theorem quotientInclusion_exact (d f g : R) :
    Function.Exact (quotientInclusion d f g)
      (Submodule.factor (refinedIdeal_le_firstIdeal d f g)) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    change (firstIdeal d f).mkQ x = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      exact ⟨((refinedIdeal d f g).comap (firstIdeal d f).subtype).mkQ ⟨x, hx⟩, rfl⟩
    · rintro ⟨y, hy⟩
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        change (refinedIdeal d f g).mkQ y.val = (refinedIdeal d f g).mkQ x at hy
        have hmem : y.val - x ∈ refinedIdeal d f g := (Submodule.Quotient.eq (refinedIdeal d f g)).mp hy
        have : x = y.val - (y.val - x) := by abel
        rw [this]
        exact (firstIdeal d f).sub_mem y.property (refinedIdeal_le_firstIdeal d f g hmem)

/-- The colon support union: any Serre predicate containing `R/I` and `R/Q`
contains `R/J`. No domain, nonzero, dimension or Ore hypothesis is needed. -/
theorem refinedIdeal_quotient_mem
    (P : (M : Type u) → [AddCommGroup M] → [Module Rᵐᵒᵖ M] → Prop)
    (hP : IsSerreClosed (R := R) P)
    (d f g L C : R) (h : f * d * L = d * C)
    (hI : P (R ⧸ firstIdeal d f)) (hQ : P (R ⧸ secondIdeal d g L)) :
    P (R ⧸ refinedIdeal d f g) := by
  have hsource := hP.of_injective (colonEmbedding d g L)
    (colonEmbedding_injective d g L) hQ
  have hIJ := hP.of_surjective (colonSurjection d f g L C h)
    (colonSurjection_surjective d f g L C h) hsource
  exact hP.of_exact (quotientInclusion d f g)
    (Submodule.factor (refinedIdeal_le_firstIdeal d f g))
    (quotientInclusion_injective d f g) (Submodule.factor_surjective _)
    (quotientInclusion_exact d f g) hIJ hI

end AlgebraicAnalysis.ColonSupport
