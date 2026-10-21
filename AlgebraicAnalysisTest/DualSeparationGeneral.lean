module
public import AlgebraicAnalysis.Module.DualSeparationGeneral
public import AlgebraicAnalysisTest.Critical

@[expose] public section

/-!
# Coordinate and quotient oracles for finite critical dual separation

The rational plane has two independent coordinate functionals. The horizontal
axis has a nonzero vertical quotient, so a germ from that axis fails the finite
dual tests. The identity passes them. Arithmetic on the quotient distinguishes
the two coordinates independently of the germ implementation.
-/

namespace AlgebraicAnalysisTest.DualSeparationGeneral
open scoped Classical
open Module Module.Germ

abbrev Plane := ℚ × ℚ

def horizontal : Submodule ℚ Plane := (LinearMap.snd ℚ ℚ ℚ).ker

def verticalQuotient : Plane ⧸ horizontal →ₗ[ℚ] ℚ :=
  horizontal.liftQ (LinearMap.snd ℚ ℚ ℚ) le_rfl

theorem rat_critical : Module.Critical ℚ 0 ℚ :=
  Module.critical_zero_of_isSimpleModule

noncomputable local instance : DivisionRing (End ℚ 0 ℚ) := End.divisionRing rat_critical

/-- The quotient retains the vertical coordinate, with its actual value. -/
theorem quotient_coordinate : verticalQuotient (horizontal.mkQ (3, 7)) = 7 := rfl

/-- The horizontal coordinate cannot descend: the quotient identifies these
points but their first coordinates differ. -/
theorem quotient_identifies_horizontal :
    horizontal.mkQ ((3, 7) : Plane) = horizontal.mkQ ((0, 7) : Plane) ∧
      (LinearMap.fst ℚ ℚ ℚ) (3, 7) ≠ (LinearMap.fst ℚ ℚ ℚ) (0, 7) := by
  constructor
  · apply (Submodule.Quotient.eq horizontal).mpr
    change (7 : ℚ) - 7 = 0
    norm_num
  · norm_num

/-- Exactness constructs a germ on the genuine nonzero quotient. -/
theorem vertical_germ_factors :
    ∃ g : Hom ℚ 0 (Plane ⧸ horizontal) ℚ,
      Hom.ofLinearMap (LinearMap.snd ℚ ℚ ℚ) =
        Hom.comp g (Hom.ofLinearMap horizontal.mkQ) := by
  apply (Hom.comp_subtype_eq_zero_iff rat_critical horizontal _).mp
  rw [← Hom.ofLinearMap_comp]
  have hz : (LinearMap.snd ℚ ℚ ℚ).comp horizontal.subtype = 0 := by
    ext x
    exact x.property
  rw [hz, Hom.ofLinearMap_zero]

/-- The ordinary quotient map supplies the factor with a checked nonzero value. -/
theorem explicit_vertical_factor :
    Hom.ofLinearMap (e := 0) (LinearMap.snd ℚ ℚ ℚ) =
      Hom.comp (Hom.ofLinearMap verticalQuotient) (Hom.ofLinearMap horizontal.mkQ) ∧
      Hom.ofLinearMap (e := 0) verticalQuotient ≠ 0 := by
  constructor
  · rw [← Hom.ofLinearMap_comp]
    rfl
  · intro hz
    have hs : Subsingleton verticalQuotient.range := (Hom.ofLinearMap_eq_zero_iff _).mp hz
    have he := hs.elim (verticalQuotient.rangeRestrict (horizontal.mkQ (3, 7))) 0
    have he' := congrArg Subtype.val he
    change (7 : ℚ) = 0 at he'
    norm_num at he'

/-- The hostile coordinate has nonzero restriction, so cannot factor as a germ. -/
theorem horizontal_germ_does_not_factor :
    ¬∃ g : Hom ℚ 0 (Plane ⧸ horizontal) ℚ,
      Hom.ofLinearMap (LinearMap.fst ℚ ℚ ℚ) =
        Hom.comp g (Hom.ofLinearMap horizontal.mkQ) := by
  intro hf
  have hz := (Hom.comp_subtype_eq_zero_iff rat_critical horizontal _).mpr hf
  rw [← Hom.ofLinearMap_comp] at hz
  have hs : Subsingleton ((LinearMap.fst ℚ ℚ ℚ).comp horizontal.subtype).range :=
    (Hom.ofLinearMap_eq_zero_iff _).mp hz
  have he := hs.elim
    (((LinearMap.fst ℚ ℚ ℚ).comp horizontal.subtype).rangeRestrict ⟨(1, 0), rfl⟩) 0
  have he' := congrArg Subtype.val he
  change (1 : ℚ) = 0 at he'
  exact one_ne_zero he'

noncomputable def planeFiltration : Module.CriticalFiltration ℚ 0 Plane :=
  Classical.choose Critical.plane_critical_filtration

theorem plane_topLength : planeFiltration.topLength 0 = 2 :=
  Classical.choose_spec Critical.plane_critical_filtration

/-- The finite family has exactly two entries, checked against ordinary
vector-space dimension by the existing independent filtration oracle. -/
theorem two_retained_factors : Fintype.card planeFiltration.TopIndex = 2 := by
  rw [Module.CriticalFiltration.card_topIndex, plane_topLength]

/-- Schur dimension is bounded by the independently known dimension two. -/
theorem plane_dual_rank_le_two :
    Module.Finite (End ℚ 0 ℚ) (Hom ℚ 0 Plane ℚ) ∧
      Module.finrank (End ℚ 0 ℚ) (Hom ℚ 0 Plane ℚ) ≤ 2 := by
  simpa only [plane_topLength] using Hom.finite_finrank_le_topLength rat_critical planeFiltration

private theorem plane_devLE : Module.DevLE ℚ 0 Plane :=
  Module.devLE_zero_iff_isArtinian.mpr inferInstance

/-- The horizontal generator misses a nonzero vertical quotient. -/
theorem horizontal_not_epic :
    ¬Hom.Epic (Hom.ofLinearMap (e := 0) (LinearMap.inl ℚ ℚ ℚ)) := by
  rw [Hom.epic_ofLinearMap_iff]
  intro hs
  have ht := Submodule.Quotient.subsingleton_iff.mp hs
  have hm : ((0, 1) : Plane) ∈ (LinearMap.inl ℚ ℚ ℚ).range := ht ▸ Submodule.mem_top
  obtain ⟨x, hx⟩ := hm
  have he := congrArg Prod.snd hx
  norm_num at he

/-- The finite dual family detects the missing coordinate. -/
theorem horizontal_fails_finite_dual :
    ¬∀ i : planeFiltration.TopIndex, Function.Injective
      (fun h : Hom ℚ 0 Plane (planeFiltration.TopFactor i) =>
        Hom.comp h (Hom.ofLinearMap (LinearMap.inl ℚ ℚ ℚ))) := by
  rw [← Hom.epic_iff_injective_comp_topFactors plane_devLE planeFiltration]
  exact horizontal_not_epic

/-- A genuine generator passes every retained critical-type test. -/
theorem identity_passes_finite_dual :
    ∀ i : planeFiltration.TopIndex, Function.Injective
      (fun h : Hom ℚ 0 Plane (planeFiltration.TopFactor i) => Hom.comp h Hom.id) := by
  intro i f g he
  simpa only [Hom.comp_id] using he

#print axioms Module.Germ.PartialHom.exists_factor_mkQ_of_critical
#print axioms Module.Germ.Hom.comp_subtype_eq_zero_iff
#print axioms Module.Germ.Hom.range_quotientLinear_eq_ker_restrictLinear
#print axioms Module.Germ.Hom.quotientLinear_injective
#print axioms Module.Germ.Hom.finite_finrank_le_topLength
#print axioms Module.Germ.Hom.finite_of_devLE
#print axioms Module.CriticalFiltration.topFactor_critical
#print axioms Module.CriticalFiltration.card_topIndex
#print axioms Module.Germ.Hom.exists_topFactor_iso_of_ne_zero
#print axioms Module.Germ.Hom.topFactor_finite_finrank_le
#print axioms Module.Germ.Hom.epic_iff_injective_comp_topFactors
#print axioms quotient_coordinate
#print axioms quotient_identifies_horizontal
#print axioms vertical_germ_factors
#print axioms explicit_vertical_factor
#print axioms horizontal_germ_does_not_factor
#print axioms two_retained_factors
#print axioms plane_dual_rank_le_two
#print axioms horizontal_not_epic
#print axioms horizontal_fails_finite_dual
#print axioms identity_passes_finite_dual

end AlgebraicAnalysisTest.DualSeparationGeneral
