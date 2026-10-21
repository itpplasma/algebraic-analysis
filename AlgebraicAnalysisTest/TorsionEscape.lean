module
public import AlgebraicAnalysis.Module.TorsionEscape

@[expose] public section

/-!
# Concrete torsion and selection oracles

The polynomial action on `ℚ × ℚ` evaluates at two distinct points. Its
annihilator is checked by coordinates, independently of the abstract common
annihilator proof. It also shows why simplicity cannot be dropped from escape.
Scalar coordinate maps independently check simultaneous witness selection and
the exact exceptional scalars of a reversed pencil.
-/

namespace AlgebraicAnalysisTest.TorsionEscape

noncomputable section

open AlgebraicAnalysis.TorsionEscape AlgebraicAnalysis.OreRightIntersection
open AlgebraicAnalysis.DenominatorTorsion MulOpposite Polynomial

def evaluations : ℚ[X] →+* ℚ × ℚ :=
  (evalRingHom 0).prod (evalRingHom 1)

local instance : Module ℚ[X]ᵐᵒᵖ (ℚ × ℚ) :=
  Module.compHom (ℚ × ℚ) (evaluations.fromOpposite (fun _ _ => Commute.all _ _))

theorem action (p : ℚ[X]) (w : ℚ × ℚ) :
    op p • w = (p.eval 0 * w.1, p.eval 1 * w.2) := rfl

local instance : SMulCommClass ℚ[X]ᵐᵒᵖ ℚ (ℚ × ℚ) where
  smul_comm p a w := by
    change (p.unop.eval 0 * (a * w.1), p.unop.eval 1 * (a * w.2)) =
      (a * (p.unop.eval 0 * w.1), a * (p.unop.eval 1 * w.2))
    ext <;> ring

theorem polynomialOre : RightOreCondition ℚ[X] := by
  intro a b ha hb
  exact ⟨b, a, mul_comm _ _, mul_ne_zero ha hb⟩

/-- Both coordinates are torsion, but their individual annihilators differ. -/
theorem evaluations_torsion : IsTorsionRight (R := ℚ[X]) (M := ℚ × ℚ) := by
  intro w
  refine ⟨X * (X - 1), mul_ne_zero X_ne_zero ?_, ?_⟩
  · simpa using (X_sub_C_ne_zero (1 : ℚ))
  · rw [action]
    ext <;> simp

/-- Coordinate oracle for annihilating the whole two-point module. -/
theorem kills_all_iff (p : ℚ[X]) :
    (∀ w : ℚ × ℚ, op p • w = 0) ↔ p.eval 0 = 0 ∧ p.eval 1 = 0 := by
  constructor
  · intro h
    constructor
    · simpa [action] using congrArg Prod.fst (h (1, 0))
    · simpa [action] using congrArg Prod.snd (h (0, 1))
  · rintro ⟨h0, h1⟩ w
    simp [action, h0, h1]

/-- Instantiate finite denominator clearing and check its result against
the independent two-point evaluation oracle. -/
example : ∃ p : ℚ[X], p ≠ 0 ∧ p.eval 0 = 0 ∧ p.eval 1 = 0 := by
  obtain ⟨p, hp, hkill⟩ := exists_common_annihilator polynomialOre evaluations_torsion
    (⊤ : Submodule ℚ (ℚ × ℚ))
  exact ⟨p, hp, (kills_all_iff p).mp (fun w => hkill w (by trivial))⟩

/-- Neither coordinate's elementary annihilator kills the other coordinate. -/
example : op (X : ℚ[X]) • ((1, 0) : ℚ × ℚ) = 0 ∧
    op (X : ℚ[X]) • ((0, 1) : ℚ × ℚ) ≠ 0 ∧
    op (X - 1 : ℚ[X]) • ((0, 1) : ℚ × ℚ) = 0 ∧
    op (X - 1 : ℚ[X]) • ((1, 0) : ℚ × ℚ) ≠ 0 := by
  simp only [action]
  norm_num

/-- Hostile control: all vectors are torsion over this Ore domain, but the
nonzero orbit with tail one is trapped in a finite-dimensional space.
Thus the simplicity hypothesis of escape is essential. -/
example : ((1, 1) : ℚ × ℚ) ≠ 0 ∧ (1 : ℚ[X]) ≠ 0 ∧
    ∀ p : ℚ[X], op (p * 1) • ((1, 1) : ℚ × ℚ) ∈
      (⊤ : Submodule ℚ (ℚ × ℚ)) := by
  simp

def scalarMap (a : ℚ) : ℚ →ₗ[ℚ] ℚ := LinearMap.toSpanSingleton ℚ ℚ a

theorem scalarMap_injective_iff (a : ℚ) :
    Function.Injective (scalarMap a) ↔ a ≠ 0 := by
  constructor
  · intro h ha
    have h10 : (1 : ℚ) = 0 := h (by simp [scalarMap, ha])
    exact one_ne_zero h10
  · intro ha x y hxy
    exact mul_right_cancel₀ ha hxy

/-- The reversed scalar pencil `2 + c` has exactly one bad parameter. -/
theorem reversed_bad_iff (c : ℚ) :
    (¬ Function.Injective (centralPencil (RingHom.id ℚ) (fun _ _ => mul_comm _ _)
      (scalarMap 2) (scalarMap 1) c)) ↔ c = -2 := by
  have heq : centralPencil (RingHom.id ℚ) (fun _ _ => mul_comm _ _)
      (scalarMap 2) (scalarMap 1) c = scalarMap (2 + c) := by
    apply LinearMap.ext
    intro x
    change x * 2 + c * (x * 1) = x * (2 + c)
    ring
  rw [heq, scalarMap_injective_iff, not_not]
  constructor <;> intro h <;> linarith

example : {c : ℚ | ¬ Function.Injective
    (centralPencil (RingHom.id ℚ) (fun _ _ => mul_comm _ _)
      (scalarMap 2) (scalarMap 1) c)} = {-2} := by
  ext c
  exact reversed_bad_iff c

example : {c : ℚ | ¬ Function.Injective
    (centralPencil (RingHom.id ℚ) (fun _ _ => mul_comm _ _)
      (scalarMap 2) (scalarMap 1) c)}.Finite :=
  reversed_centralPencil_injective_finite _ _ _ _
    ((scalarMap_injective_iff 1).mpr one_ne_zero)

def diagonalScalars : ℚ →+* ℚ × ℚ := (RingHom.id ℚ).prod (RingHom.id ℚ)

def coordinateFamily (i : Bool) (r : ℚ × ℚ) : ℚ →ₗ[ℚ] ℚ :=
  scalarMap (if i then r.2 else r.1)

/-- Each coordinate family is good somewhere, with different elementary
witnesses. The abstract selection must find one pair good for both. -/
example : ∃ r : ℚ × ℚ, r.1 ≠ 0 ∧ r.2 ≠ 0 := by
  have hF (i : Bool) (r t : ℚ × ℚ) (c d : ℚ) :
      coordinateFamily i (r + diagonalScalars c * t) d =
        coordinateFamily i r d + c • coordinateFamily i t d := by
    cases i <;> simp [coordinateFamily, scalarMap, diagonalScalars,
      mul_add, mul_left_comm, mul_comm]
  have hgood (i : Bool) (_ : i ∈ (Finset.univ : Finset Bool)) :
      ∃ r, Function.Injective (coordinateFamily i r) := by
    cases i
    · exact ⟨(1, 0), (scalarMap_injective_iff 1).mpr one_ne_zero⟩
    · exact ⟨(0, 1), (scalarMap_injective_iff 1).mpr one_ne_zero⟩
  obtain ⟨r, hr⟩ := exists_simultaneously_injective diagonalScalars
    (fun _ => RingHom.id ℚ) (fun _ _ _ => mul_comm _ _) coordinateFamily hF
      Finset.univ hgood
  exact ⟨r, (scalarMap_injective_iff _).mp (hr false (Finset.mem_univ _)),
    (scalarMap_injective_iff _).mp (hr true (Finset.mem_univ _))⟩

/-- Independent arithmetic witness for the same simultaneous test. -/
example : Function.Injective (coordinateFamily false (1, 1)) ∧
    Function.Injective (coordinateFamily true (1, 1)) := by
  exact ⟨(scalarMap_injective_iff 1).mpr one_ne_zero,
    (scalarMap_injective_iff 1).mpr one_ne_zero⟩

/-- A field is a simple Ore domain. Its regular module has no nonzero
torsion vectors, as is checked directly by multiplication. -/
example : ¬ IsTorsionRight (R := ℚ) (M := ℚ) := by
  intro h
  obtain ⟨r, hr, hkill⟩ := h 1
  exact hr (by simpa using hkill)

/-- The escape API agrees with that independent field obstruction. -/
example (h : IsTorsionRight (R := ℚ) (M := ℚ)) : False := by
  have hOre : RightOreCondition ℚ := by
    intro a b ha hb
    exact ⟨b, a, mul_comm _ _, mul_ne_zero ha hb⟩
  obtain ⟨r, hr⟩ := exists_smul_mul_not_mem (E := ℚ) hOre h one_ne_zero
    (b := (1 : ℚ)) one_ne_zero (⊤ : Submodule ℚ ℚ)
  exact hr (by trivial)

#print axioms AlgebraicAnalysis.TorsionEscape.exists_common_annihilator
#print axioms AlgebraicAnalysis.TorsionEscape.exists_smul_mul_not_mem
#print axioms AlgebraicAnalysis.TorsionEscape.centralPencil_injective_finite
#print axioms AlgebraicAnalysis.TorsionEscape.reversed_centralPencil_injective_finite
#print axioms AlgebraicAnalysis.TorsionEscape.exists_injective_of_escape
#print axioms AlgebraicAnalysis.TorsionEscape.exists_injective_right_mul
#print axioms AlgebraicAnalysis.TorsionEscape.exists_simultaneously_injective
#print axioms AlgebraicAnalysis.TorsionEscape.exists_affine_direction
#print axioms AlgebraicAnalysis.TorsionEscape.exists_affine_source

end

end AlgebraicAnalysisTest.TorsionEscape
