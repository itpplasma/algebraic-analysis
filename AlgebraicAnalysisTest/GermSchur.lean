module
public import AlgebraicAnalysis.Module.DualSeparation
public import AlgebraicAnalysisTest.Critical
public import AlgebraicAnalysisTest.Germ

@[expose] public section

/-!
# Arithmetic oracles for critical Schur germs

Multiplication by two on the integers has no ordinary inverse, but becomes
invertible at stratum one. Over the prime field of five elements, two and
three are explicit mutual inverses. The rational right-regular example
checks the section action against ordinary rational multiplication.
-/

namespace AlgebraicAnalysisTest.GermSchur

open Module Module.Germ MulOpposite

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

noncomputable local instance : DivisionRing (End ℤ 1 ℤ) :=
  End.divisionRing Critical.int_critical_one

/-- The hostile ordinary-endomorphism control: no integer map halves one. -/
theorem twice_no_ordinary_inverse :
    ¬∃ g : ℤ →ₗ[ℤ] ℤ, Germ.twice.comp g = LinearMap.id := by
  rintro ⟨g, hg⟩
  have he := LinearMap.congr_fun hg 1
  change 2 * g 1 = 1 at he
  omega

/-- The same nonunit becomes a unit in the critical germ division ring. -/
theorem twice_germ_inverse :
    let f : End ℤ 1 ℤ := Hom.ofLinearMap Germ.twice
    f * f⁻¹ = 1 ∧ f⁻¹ * f = 1 :=
  ⟨mul_inv_cancel₀ Germ.twice_germ_ne_zero, inv_mul_cancel₀ Germ.twice_germ_ne_zero⟩

/-- Dual separation detects the finite cokernel of doubling as small. -/
theorem twice_dual_injective :
    Function.Injective (fun h : End ℤ 1 ℤ =>
      Hom.comp h (Hom.ofLinearMap Germ.twice)) :=
  (Hom.epic_iff_injective_comp_of_critical Critical.int_critical_one _).mp
    Germ.twice_epic_one_not_zero.1

/-- The zero germ fails the dual test: the identity germ survives. -/
theorem zero_dual_not_injective :
    ¬Function.Injective (fun h : End ℤ 1 ℤ => Hom.comp h (0 : Hom ℤ 1 ℤ ℤ)) := by
  intro hi
  have he : Hom.comp (1 : End ℤ 1 ℤ) (0 : Hom ℤ 1 ℤ ℤ) =
      Hom.comp (0 : End ℤ 1 ℤ) (0 : Hom ℤ 1 ℤ ℤ) :=
    (PartialHom.comp_zero _).trans (PartialHom.zero_comp _).symm
  exact one_ne_zero (hi he)

def primeMul (a : ZMod 5) : ZMod 5 →ₗ[ℤ] ZMod 5 := LinearMap.mulLeft ℤ a

/-- An explicit prime-field multiplication oracle, independent of chosen inverses. -/
theorem prime_two_three :
    (Hom.ofLinearMap (e := 0) (primeMul 2) : End ℤ 0 (ZMod 5)) *
      Hom.ofLinearMap (primeMul 3) = 1 := by
  change Hom.comp (Hom.ofLinearMap _) (Hom.ofLinearMap _) = Hom.id
  rw [← Hom.ofLinearMap_comp]
  have he : (primeMul 2).comp (primeMul 3) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (2 : ZMod 5) * (3 * x) = x
    rw [← mul_assoc, show (2 : ZMod 5) * 3 = 1 by decide, one_mul]
  rw [he, Hom.ofLinearMap_id]

/-- The prime-field germ is nonzero, checked at the ordinary element one. -/
theorem prime_two_ne_zero :
    (Hom.ofLinearMap (e := 0) (primeMul 2) : End ℤ 0 (ZMod 5)) ≠ 0 := by
  intro hz
  have hs := (Hom.ofLinearMap_eq_zero_iff (primeMul 2)).mp hz
  have hb := Submodule.subsingleton_iff_eq_bot.mp hs
  have hm := LinearMap.mem_range_self (primeMul 2) 1
  have he : primeMul 2 1 = 0 := hb.le hm
  norm_num [primeMul, LinearMap.mulLeft_apply] at he
  exact (by decide : (2 : ZMod 5) ≠ 0) he

/-- Zero-dimensional critical Hom spaces have the expected rank bound one. -/
theorem prime_hom_rank_le_one :
    letI := End.divisionRing (Critical.zmod_critical_zero 5)
    Module.finrank (End ℤ 0 (ZMod 5)) (Hom ℤ 0 (ZMod 5) (ZMod 5)) ≤ 1 :=
  Hom.finrank_le_one_of_critical (Critical.zmod_critical_zero 5) (Critical.zmod_critical_zero 5)

private theorem rat_critical : Module.Critical ℚᵐᵒᵖ 0 ℚᵐᵒᵖ :=
  Module.critical_zero_of_isSimpleModule

/-- The right section action agrees with multiplying the embedded rational
element by the displayed scalars in order. -/
theorem rational_section_arithmetic :
    op (5 : ℚ) • (op (2 : ℚ) •
      Section.ofElement (R := ℚ) (e := 0) (op (3 : ℚ))) =
      Section.ofElement (R := ℚ) (e := 0) (op (30 : ℚ)) := by
  rw [← map_smul, ← map_smul]
  congr 1
  apply unop_injective
  norm_num

/-- Uniformity is tested on actual section submodules, with right scalars. -/
example (U V : Submodule ℚᵐᵒᵖ (Section ℚ 0 ℚᵐᵒᵖ)) (hU : U ≠ ⊥) (hV : V ≠ ⊥) :
    U ⊓ V ≠ ⊥ := Section.inf_ne_bot rat_critical hU hV

#print axioms Module.Germ.Hom.exists_inverse_of_critical
#print axioms Module.Germ.End.divisionRing
#print axioms Module.Germ.End.centerMap
#print axioms Module.Germ.End.centralMap_comp_injective
#print axioms Module.Germ.Section.ofElement_injective
#print axioms Module.Germ.Section.smul_mk_eq_ofElement
#print axioms Module.Germ.Section.exists_smul_eq_ofElement
#print axioms Module.Germ.Section.comap_ofElement_ne_bot
#print axioms Module.Germ.Section.inf_ne_bot
#print axioms Module.Germ.Section.eq_bot_of_locSmall
#print axioms Module.Germ.Section.torsion
#print axioms Module.DevLE.exists_critical_quotient
#print axioms Module.Germ.Hom.finite_of_critical
#print axioms Module.Germ.Hom.finrank_le_one_of_critical
#print axioms Module.Germ.Hom.epic_iff_injective_comp_of_critical
#print axioms twice_no_ordinary_inverse
#print axioms twice_germ_inverse
#print axioms twice_dual_injective
#print axioms zero_dual_not_injective
#print axioms prime_two_three
#print axioms prime_two_ne_zero
#print axioms prime_hom_rank_le_one
#print axioms rational_section_arithmetic

end AlgebraicAnalysisTest.GermSchur
