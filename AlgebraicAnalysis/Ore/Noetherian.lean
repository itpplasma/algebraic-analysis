module
public import AlgebraicAnalysis.Ore.RightIntersection
public import AlgebraicAnalysis.Module.DenominatorTorsion

@[expose] public section

/-!
# Right Ore conditions and right Noetherian domains

Right ideals and right modules use scalars in the opposite ring. The ascending
chain argument uses the finite sums of `b^j aR`: if `aR` and `bR` have zero
intersection, cancellation makes every new summand contribute a new element.
-/

namespace AlgebraicAnalysis.OreRightIntersection

open MulOpposite nonZeroDivisors
open DenominatorTorsion

variable {R : Type*} [Ring R] [IsDomain R]

/-- The common-right-multiple condition is Mathlib's left Ore condition on
all nonzero elements of the opposite ring. `Nonempty` forgets the chosen
numerator and denominator functions in `OreSet`. -/
theorem rightOreCondition_iff_nonempty_oreSet :
    RightOreCondition R ↔ Nonempty (OreLocalization.OreSet (Rᵐᵒᵖ)⁰) := by
  rw [OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors]
  constructor
  · intro h r s
    by_cases hr : r = 0
    · exact ⟨0, 1, by simp [hr]⟩
    obtain ⟨x, y, hxy, hne⟩ := h (a := unop r) (b := unop s.val)
      (by simpa using hr) (by simpa using nonZeroDivisors.coe_ne_zero s)
    have hx : x ≠ 0 := by intro hx; simp [hx] at hne
    exact ⟨op y, ⟨op x, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa using hx)⟩,
      unop_injective hxy⟩
  · intro h a b ha hb
    obtain ⟨y, x, hxy⟩ := h (op a)
      ⟨op b, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa using hb)⟩
    refine ⟨unop x.val, unop y, congrArg unop hxy, mul_ne_zero ha ?_⟩
    simpa using nonZeroDivisors.coe_ne_zero x

/-- Finite partial sums of `aR + baR + ⋯`, written recursively to expose
cancellation of the lowest power of `b`. -/
private def partialSum (a b : R) : ℕ → Submodule Rᵐᵒᵖ R
  | 0 => ⊥
  | n + 1 => principalRightIdeal a ⊔ (partialSum a b n).map (leftMulLinear b)

omit [IsDomain R] in
private theorem partialSum_mono (a b : R) : Monotone (partialSum a b) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact sup_le_sup_left (Submodule.map_mono ih) _

omit [IsDomain R] in
private theorem pow_mul_mem_partialSum (a b : R) (n : ℕ) :
    b ^ n * a ∈ partialSum a b (n + 1) := by
  induction n with
  | zero => exact Submodule.mem_sup_left (by exact ⟨1, by simp [leftMulLinear]⟩)
  | succ n ih =>
    apply Submodule.mem_sup_right
    exact ⟨b ^ n * a, ih, by simp [leftMulLinear, pow_succ', mul_assoc]⟩

private theorem pow_mul_not_mem_partialSum (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdis : ∀ x y : R, a * x = b * y → a * x = 0) (n : ℕ) :
    b ^ n * a ∉ partialSum a b n := by
  induction n with
  | zero => simpa [partialSum] using ha
  | succ n ih =>
    intro hm
    obtain ⟨u, ⟨x, rfl⟩, v, ⟨y, hy, rfl⟩, huv⟩ := Submodule.mem_sup.mp hm
    change a * x + b * y = b ^ (n + 1) * a at huv
    have heq : a * x = b * (b ^ n * a - y) := by
      rw [mul_sub, ← mul_assoc, ← pow_succ']
      exact eq_sub_of_add_eq huv
    have hax := hdis x _ heq
    rw [hax, zero_add, pow_succ', mul_assoc] at huv
    exact ih ((mul_left_cancel₀ hb huv) ▸ hy)

/-- A right Noetherian domain has nonzero common right multiples.
The Noetherian hypothesis is on the right regular module, not the left one. -/
theorem rightOreCondition_of_isNoetherian [IsNoetherian Rᵐᵒᵖ R] :
    RightOreCondition R := by
  intro a b ha hb
  by_contra h
  have hdis : ∀ x y : R, a * x = b * y → a * x = 0 := by
    intro x y hxy
    by_contra hne
    exact h ⟨x, y, hxy, hne⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian Rᵐᵒᵖ R)
    ⟨partialSum a b, partialSum_mono a b⟩
  have heq : partialSum a b n = partialSum a b (n + 1) := hn (n + 1) (Nat.le_succ n)
  apply pow_mul_not_mem_partialSum a b ha hb hdis n
  rw [heq]
  exact pow_mul_mem_partialSum a b n

/-- The ring-class version of the right Noetherian Ore theorem. -/
theorem rightOreCondition_of_isNoetherianRing [IsNoetherianRing Rᵐᵒᵖ] :
    RightOreCondition R := by
  let : IsNoetherian Rᵐᵒᵖ R := isNoetherian_of_injective
    (opLinearEquiv Rᵐᵒᵖ : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ).toLinearMap
    (opLinearEquiv Rᵐᵒᵖ).injective
  exact rightOreCondition_of_isNoetherian

/-- A choice of Mathlib Ore data for a right Noetherian domain. This is not
a global instance, so it does not override other choices of Ore data. -/
@[instance_reducible]
noncomputable def oreSetOppositeOfIsNoetherian [IsNoetherian Rᵐᵒᵖ R] :
    OreLocalization.OreSet (Rᵐᵒᵖ)⁰ :=
  (rightOreCondition_iff_nonempty_oreSet.mp rightOreCondition_of_isNoetherian).some

end AlgebraicAnalysis.OreRightIntersection

namespace AlgebraicAnalysis.DenominatorTorsion

open MulOpposite

variable {R : Type*} [Ring R]
variable {M N : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [AddCommGroup N] [Module Rᵐᵒᵖ N]

/-- Torsion passes to a submodule, or any module embedded in a torsion module. -/
theorem isTorsionRight_of_injective (f : M →ₗ[Rᵐᵒᵖ] N) (hf : Function.Injective f)
    (hN : IsTorsionRight (R := R) (M := N)) : IsTorsionRight (R := R) (M := M) := by
  intro m
  obtain ⟨s, hs, hsm⟩ := hN (f m)
  exact ⟨s, hs, hf (by simpa using hsm)⟩

/-- Torsion passes to any quotient presented by a surjective linear map. -/
theorem isTorsionRight_of_surjective (f : M →ₗ[Rᵐᵒᵖ] N) (hf : Function.Surjective f)
    (hM : IsTorsionRight (R := R) (M := M)) : IsTorsionRight (R := R) (M := N) := by
  intro n
  obtain ⟨m, rfl⟩ := hf n
  obtain ⟨s, hs, hsm⟩ := hM m
  exact ⟨s, hs, by simpa using congrArg f hsm⟩

/-- Torsion of a principal quotient implies torsion of every larger ideal's quotient. -/
theorem quotient_isTorsion_of_principal_le [IsDomain R]
    (hOre : OreRightIntersection.RightOreCondition R) (q : R) (hq : q ≠ 0)
    (I : Submodule Rᵐᵒᵖ R) (hI : principalRightIdeal q ≤ I) :
    IsTorsionRight (R := R) (M := R ⧸ I) := by
  let := (OreRightIntersection.rightOreCondition_iff_nonempty_oreSet.mp hOre).some
  exact isTorsionRight_of_surjective (Submodule.factor hI)
    (Submodule.factor_surjective hI) (principal_quotient_isTorsion q hq)

/-- Over a right Ore domain, torsion elements form a right submodule. -/
def torsionSubmodule [IsDomain R] (hOre : OreRightIntersection.RightOreCondition R) :
    Submodule Rᵐᵒᵖ M where
  carrier := {m | ∃ s : R, s ≠ 0 ∧ op s • m = 0}
  zero_mem' := ⟨1, one_ne_zero, smul_zero _⟩
  add_mem' := by
    rintro m n ⟨a, ha, hma⟩ ⟨b, hb, hnb⟩
    obtain ⟨x, y, hxy, hne⟩ := hOre ha hb
    refine ⟨a * x, hne, ?_⟩
    rw [smul_add]
    have hm : op (a * x) • m = 0 := by
      rw [op_mul, mul_smul, hma, smul_zero]
    have hn : op (a * x) • n = 0 := by
      rw [hxy, op_mul, mul_smul, hnb, smul_zero]
    rw [hm, hn, add_zero]
  smul_mem' := by
    rintro r m ⟨a, ha, hma⟩
    by_cases hr : unop r = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      have : r = 0 := unop_injective hr
      simp [this]
    obtain ⟨x, y, hxy, hne⟩ := hOre hr ha
    have hx : x ≠ 0 := by intro hx; simp [hx] at hne
    refine ⟨x, hx, ?_⟩
    rw [← mul_smul]
    change op (unop r * x) • m = 0
    rw [hxy, op_mul, mul_smul, hma, smul_zero]

end AlgebraicAnalysis.DenominatorTorsion
