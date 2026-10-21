module
import AlgebraicAnalysis.Ore.Noetherian
import AlgebraicAnalysis.Module.ColonSupport

/-! Independent arithmetic and noncommutative matrix oracles for Ore and colon maps. -/

open AlgebraicAnalysis AlgebraicAnalysis.OreRightIntersection
open AlgebraicAnalysis.DenominatorTorsion AlgebraicAnalysis.ColonSupport
open MulOpposite nonZeroDivisors

namespace AlgebraicAnalysisTest.OreColon

-- The right regular module over the integers is Noetherian via its ordinary
-- integer-module structure; no Ore instance is used to produce this fact.
example : RightOreCondition ℤ := by
  let : IsNoetherian ℤᵐᵒᵖ ℤ := isNoetherian_of_tower ℤ inferInstance
  exact rightOreCondition_of_isNoetherian

-- An independent arithmetic common multiple, including its nonvanishing.
example : ∃ x y : ℤ, 6 * x = 15 * y ∧ 6 * x ≠ 0 := by
  exact ⟨5, 2, by norm_num, by norm_num⟩

example : Nonempty (OreLocalization.OreSet (ℤᵐᵒᵖ)⁰) := by
  apply rightOreCondition_iff_nonempty_oreSet.mp
  intro a b ha hb
  exact ⟨b, a, mul_comm _ _, mul_ne_zero ha hb⟩

-- This checks the orientation against Mathlib's already existing Ore data.
example : RightOreCondition ℤ :=
  rightOreCondition_iff_nonempty_oreSet.mpr ⟨inferInstance⟩

-- Independently instantiate the class with Mathlib's Noetherian predicate.
theorem noetherianSerre (R : Type*) [Ring R] :
    IsSerreClosed (R := R) (fun M _ _ => IsNoetherian Rᵐᵒᵖ M) where
  of_injective := by
    intro M N _ _ _ _ i hi hN
    let := hN
    exact isNoetherian_of_injective i hi
  of_surjective := by
    intro M N _ _ _ _ p hp hM
    let := hM
    exact isNoetherian_of_surjective p (LinearMap.range_eq_top.mpr hp)
  of_exact := by
    intro A B C _ _ _ _ _ _ i p _ _ hex hA hC
    let := hA
    let := hC
    exact isNoetherian_of_range_eq_ker i p (LinearMap.exact_iff.mp hex).symm

abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 2)

-- Fix the additive structure inherited from the matrix ring for quotients.
local instance : AddCommGroup Mat := (inferInstance : Ring Mat).toAddCommGroup

def e11 : Mat := !![1, 0; 0, 0]
def e21 : Mat := !![0, 0; 1, 0]
def e22 : Mat := !![0, 0; 0, 1]

-- A direct row calculation, independent of the colon machinery.
theorem mem_e11_ideal (x : Mat) :
    x ∈ principalRightIdeal e11 ↔ x 1 0 = 0 ∧ x 1 1 = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    simp [leftMulLinear, e11, Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two]
  · rintro ⟨h0, h1⟩
    refine ⟨x, ?_⟩
    change e11 * x = x
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e11, Matrix.mul_apply, Fin.sum_univ_two, h0, h1]

-- K consists of the matrices whose first row is zero, and is proper.
theorem mem_matrix_colon (x : Mat) :
    x ∈ colon e11 e21 ↔ x 0 0 = 0 ∧ x 0 1 = 0 := by
  change e21 * e11 * x ∈ principalRightIdeal e11 ↔ _
  rw [mem_e11_ideal]
  simp [e11, e21, Matrix.mul_apply, Fin.sum_univ_two]

example : e22 ∈ colon e11 e21 ∧ e11 ∉ colon e11 e21 := by
  rw [mem_matrix_colon, mem_matrix_colon]
  decide

-- fdL = dC with d=e11, f=g=e21, L=e22 and C=0.
theorem matrix_relation : e21 * e11 * e22 = e11 * (0 : Mat) := by decide

theorem matrix_secondIdeal : secondIdeal e11 e21 e22 = principalRightIdeal e11 := by
  apply le_antisymm
  · apply sup_le le_rfl
    rintro x ⟨s, rfl⟩
    change e21 * e11 * e22 * s ∈ principalRightIdeal e11
    rw [matrix_relation, mul_zero, zero_mul]
    exact Submodule.zero_mem _
  · exact le_sup_left

theorem matrix_refinedIdeal : refinedIdeal e11 e21 e21 = principalRightIdeal e11 := by
  apply le_antisymm
  · apply sup_le le_rfl
    rintro x ⟨s, hs, rfl⟩
    change e21 * e11 * s ∈ principalRightIdeal e11
    exact hs
  · exact le_sup_left

theorem matrix_image : e21 * e11 * e11 = e21 := by decide

theorem matrix_image_mem : e21 ∈ firstIdeal e11 e21 :=
  Submodule.mem_sup_right ⟨e11, matrix_image⟩

-- The embedding sends a nonzero first-row class to a nonzero second-row class.
example : colonEmbedding e11 e21 e22 ((sourceIdeal e11 e21 e22).mkQ e11) =
    (secondIdeal e11 e21 e22).mkQ e21 := by
  rw [colonEmbedding_mk]
  congr 1
  decide

example : colonEmbedding e11 e21 e22 ((sourceIdeal e11 e21 e22).mkQ e11) ≠ 0 := by
  rw [colonEmbedding_mk]
  intro hz
  have hm : e21 * e11 * e11 ∈ secondIdeal e11 e21 e22 :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  rw [matrix_secondIdeal, mem_e11_ideal] at hm
  exact (by decide : ¬ ((e21 * e11 * e11) 1 0 = 0 ∧ (e21 * e11 * e11) 1 1 = 0)) hm

-- Reversing gd gives zero in this example, so the orientation is observable.
example : e11 * e21 * e11 = (0 : Mat) ∧ e21 * e11 * e11 ≠ (0 : Mat) := by decide

example : Function.Injective (colonEmbedding e11 e21 e22) :=
  colonEmbedding_injective _ _ _

example : Function.Surjective
    (colonSurjection e11 e21 e21 e22 0 matrix_relation) :=
  colonSurjection_surjective _ _ _ _ _ _

-- Check the second map's literal representative and that it also is nonzero.
example : colonSurjection e11 e21 e21 e22 0 matrix_relation
    ((sourceIdeal e11 e21 e22).mkQ e11) =
    ((refinedIdeal e11 e21 e21).comap (firstIdeal e11 e21).subtype).mkQ
      ⟨e21, matrix_image_mem⟩ := by
  rw [colonSurjection_mk]
  congr 1
  apply Subtype.ext
  decide

example : colonSurjection e11 e21 e21 e22 0 matrix_relation
    ((sourceIdeal e11 e21 e22).mkQ e11) ≠ 0 := by
  rw [colonSurjection_mk]
  intro hz
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
  change e21 * e11 * e11 ∈ refinedIdeal e11 e21 e21 at hm
  rw [matrix_refinedIdeal, mem_e11_ideal] at hm
  exact (by decide : ¬ ((e21 * e11 * e11) 1 0 = 0 ∧ (e21 * e11 * e11) 1 1 = 0)) hm

example : IsNoetherian Matᵐᵒᵖ (Mat ⧸ refinedIdeal e11 e21 e21) :=
  refinedIdeal_quotient_mem (fun M _ _ => IsNoetherian Matᵐᵒᵖ M)
    (noetherianSerre Mat) e11 e21 e21 e22 0 matrix_relation inferInstance inferInstance

example : refinedIdeal e11 e21 e21 ≤ firstIdeal e11 (e21 + e21) := by
  simpa using refinedIdeal_le_pencil e11 e21 e21 1 (fun x => by simp)

#print axioms AlgebraicAnalysis.OreRightIntersection.rightOreCondition_of_isNoetherianRing
#print axioms AlgebraicAnalysis.OreRightIntersection.rightOreCondition_iff_nonempty_oreSet
#print axioms AlgebraicAnalysis.OreRightIntersection.rightOreCondition_of_isNoetherian
#print axioms AlgebraicAnalysis.OreRightIntersection.oreSetOppositeOfIsNoetherian
#print axioms AlgebraicAnalysis.DenominatorTorsion.isTorsionRight_of_injective
#print axioms AlgebraicAnalysis.DenominatorTorsion.isTorsionRight_of_surjective
#print axioms AlgebraicAnalysis.DenominatorTorsion.quotient_isTorsion_of_principal_le
#print axioms AlgebraicAnalysis.DenominatorTorsion.torsionSubmodule
#print axioms AlgebraicAnalysis.ColonSupport.refinedIdeal_le_firstIdeal
#print axioms AlgebraicAnalysis.ColonSupport.refinedIdeal_le_pencil
#print axioms AlgebraicAnalysis.ColonSupport.comap_secondIdeal
#print axioms AlgebraicAnalysis.ColonSupport.colonEmbedding
#print axioms AlgebraicAnalysis.ColonSupport.colonEmbedding_injective
#print axioms AlgebraicAnalysis.ColonSupport.colonSurjection
#print axioms AlgebraicAnalysis.ColonSupport.colonSurjection_surjective
#print axioms AlgebraicAnalysis.ColonSupport.quotientInclusion_injective
#print axioms AlgebraicAnalysis.ColonSupport.quotientInclusion_exact
#print axioms AlgebraicAnalysis.ColonSupport.refinedIdeal_quotient_mem

end AlgebraicAnalysisTest.OreColon
