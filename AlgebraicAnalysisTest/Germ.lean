module
public import AlgebraicAnalysis.Module.Germ
public import AlgebraicAnalysisTest.Deviation

@[expose] public section

/-!
# Integer and finite-module germ oracles

The arithmetic oracle is the nonzero finite cokernel of multiplication by two
on the integers. Its partial inverse is defined on the even integers. A second
oracle uses noncommuting coordinate maps on `ℤ²`; finite characteristic targets
check that a nonzero actual map can have zero germ.
-/

namespace AlgebraicAnalysisTest.Germ

open Module Module.Germ
open scoped DirectSum

def twice : ℤ →ₗ[ℤ] ℤ := LinearMap.mulLeft ℤ 2

theorem twice_injective : Function.Injective twice :=
  fun _ _ h => mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h

/-- A nonzero finite cokernel is killed at stratum one, but not stratum zero. -/
theorem twice_epic_one_not_zero :
    Hom.Epic (Hom.ofLinearMap (e := 1) twice) ∧
      ¬Hom.Epic (Hom.ofLinearMap (e := 0) twice) := by
  constructor
  · exact (Hom.epic_ofLinearMap_iff twice).mpr Deviation.int_mul_two_quotient.1
  · rw [Hom.epic_ofLinearMap_iff]
    exact Deviation.int_mul_two_quotient.2

/-- Multiplication by two survives: its image is isomorphic to the non-Artinian integers. -/
theorem twice_germ_ne_zero : Hom.ofLinearMap (e := 1) twice ≠ 0 := by
  intro h
  have hs := (Hom.ofLinearMap_eq_zero_iff twice).mp h
  exact Deviation.int_not_devLE_zero
    ((small_linearEquiv_iff 1 (LinearEquiv.ofInjective twice twice_injective)).mpr hs)

noncomputable def half : Representative ℤ 1 ℤ ℤ :=
  ⟨⟨twice.range, (LinearEquiv.ofInjective twice twice_injective).symm.toLinearMap⟩,
    Deviation.int_mul_two_quotient.1⟩

/-- Division by two on the even integers is a two-sided germ inverse. -/
theorem half_twice :
    (PartialHom.mk half).comp (PartialHom.ofLinearMap twice) =
      PartialHom.ofLinearMap (e := 1) (LinearMap.id : ℤ →ₗ[ℤ] ℤ) ∧
    (PartialHom.ofLinearMap twice).comp (PartialHom.mk half) =
      PartialHom.ofLinearMap (e := 1) (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  constructor
  · apply Quotient.sound
    apply Representative.rel_of_eq
    intro x hx hy
    exact (LinearEquiv.ofInjective twice twice_injective).symm_apply_apply x
  · apply Quotient.sound
    apply Representative.rel_of_eq
    intro x hx hy
    have hx' : x ∈ twice.range := half.pullback_le _ hx
    exact congrArg Subtype.val
      ((LinearEquiv.ofInjective twice twice_injective).apply_symm_apply ⟨x, hx'⟩)

/-- Odd multiplication preserves the dense even-integer domain, with exact membership. -/
theorem dense_even_preimage :
    Dense ℤ 1 (twice.range.comap (LinearMap.mulLeft ℤ (3 : ℤ))) ∧
      twice.range.comap (LinearMap.mulLeft ℤ (3 : ℤ)) = twice.range := by
  refine ⟨Dense.comap (show Dense ℤ 1 twice.range from Deviation.int_mul_two_quotient.1) _, ?_⟩
  ext x
  change (∃ z : ℤ, 2 * z = 3 * x) ↔ ∃ z : ℤ, 2 * z = x
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z - x, by omega⟩
  · rintro ⟨z, hz⟩
    exact ⟨3 * z, by omega⟩

/-- Infinite sums of finite nonzero modules belong to the locally small class. -/
theorem infinite_sum_locSmall : LocSmall ℤ 1 (⨁ _ : ℕ, ZMod 2) :=
  LocSmall.directSum fun _ =>
    Small.locSmall (R := ℤ) (e := 1) (M := ZMod 2)
      (devLE_zero_iff_isArtinian.mpr isArtinian_of_finite)

def castSix : ℤ →ₗ[ℤ] ZMod 6 :=
  { toFun := fun z => z • (1 : ZMod 6)
    map_add' := fun x y => add_smul x y 1
    map_smul' := fun r x => mul_smul r x 1 }

/-- An actually nonzero homomorphism can vanish as a germ. -/
theorem finite_target_zero_germ :
    castSix 1 ≠ 0 ∧ Hom.ofLinearMap (e := 1) castSix = 0 := by
  refine ⟨by simpa only [castSix, LinearMap.coe_mk, AddHom.coe_mk, one_smul] using
    (show (1 : ZMod 6) ≠ 0 by decide), (Hom.ofLinearMap_eq_zero_iff castSix).mpr ?_⟩
  exact (devLE_zero_iff_isArtinian.mpr (isArtinian_of_finite (R := ℤ))).submodule _

def shiftLeft : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) :=
  (LinearMap.inl ℤ ℤ ℤ).comp (LinearMap.snd ℤ ℤ ℤ)

def shiftRight : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) :=
  (LinearMap.inr ℤ ℤ ℤ).comp (LinearMap.fst ℤ ℤ ℤ)

/-- The two composition orders remain distinct after passage to germs. -/
theorem composition_order :
    Hom.comp (Hom.ofLinearMap (e := 1) shiftLeft) (Hom.ofLinearMap shiftRight) ≠
      Hom.comp (Hom.ofLinearMap (e := 1) shiftRight) (Hom.ofLinearMap shiftLeft) := by
  intro h
  have he : Hom.ofLinearMap (e := 1)
      (shiftLeft.comp shiftRight - shiftRight.comp shiftLeft) = 0 := by
    have hs : Hom.ofLinearMap (e := 1) (shiftLeft.comp shiftRight) =
        Hom.ofLinearMap (e := 1) (shiftRight.comp shiftLeft) := by
      simpa only [Hom.ofLinearMap_comp] using h
    have ha := Hom.ofLinearMap_add (e := 1)
      (shiftLeft.comp shiftRight - shiftRight.comp shiftLeft) (shiftRight.comp shiftLeft)
    rw [sub_add_cancel, hs] at ha
    exact add_right_cancel (ha.symm.trans (zero_add _).symm)
  have hs := (Hom.ofLinearMap_eq_zero_iff _).mp he
  let j : ℤ →ₗ[ℤ] LinearMap.range
      (shiftLeft.comp shiftRight - shiftRight.comp shiftLeft) :=
    { toFun := fun x => ⟨(x, 0), ⟨(x, 0), by simp [shiftLeft, shiftRight]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := by intro r x; apply Subtype.ext; simp }
  exact Deviation.int_not_devLE_zero (hs.of_injective j (by
    intro x y hxy
    exact congrArg (fun z => z.val.1) hxy))

/-- A nonzero finite-target map with the zero target denominator. -/
def finitePair : Pair ℤ 1 ℤ (ZMod 6) := Pair.ofLinearMap castSix

/-- The zero map with the entire finite target as denominator. -/
def finiteZeroPair : Pair ℤ 1 ℤ (ZMod 6) :=
  ⟨⊤, dense_top, ⊤,
    devLE_zero_iff_isArtinian.mpr isArtinian_of_finite, 0⟩

/-- Enlarging a genuinely zero denominator can kill a genuinely nonzero map. -/
theorem finite_pair_target_enlargement :
    finitePair.toHom = finiteZeroPair.toHom ∧
      finitePair.map ⟨1, Submodule.mem_top⟩ ≠ 0 := by
  constructor
  · apply (Pair.toHom_eq_toHom_iff finitePair finiteZeroPair).mpr
    exact ⟨⊤, dense_top, le_rfl, le_rfl, ⊤,
      devLE_zero_iff_isArtinian.mpr isArtinian_of_finite, le_top, le_rfl,
      fun _ => Subsingleton.elim _ _⟩
  · intro h
    have hz : castSix 1 ∈ (⊥ : Submodule ℤ (ZMod 6)) :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    exact finite_target_zero_germ.1 hz

#print axioms Module.LocSmall.of_submodule_quotient
#print axioms Module.LocSmall.directSum
#print axioms Module.small_smallRadical
#print axioms Module.eq_bot_of_small_quotient_radical
#print axioms Module.Dense.inf
#print axioms Module.Dense.comap
#print axioms Module.Germ.Representative.Rel.trans
#print axioms Module.Germ.Representative.Rel.comp
#print axioms Module.Germ.PartialHom.instAddCommGroup
#print axioms Module.Germ.Hom.comp_assoc
#print axioms Module.Germ.Hom.add_comp
#print axioms Module.Germ.Hom.comp_add
#print axioms Module.Germ.Hom.ofLinearMap_eq_zero_iff
#print axioms Module.Germ.Hom.epic_ofLinearMap_iff
#print axioms Module.Germ.PartialHom.epic_iff_right_cancel
#print axioms Module.Germ.Pair.toHom_eq_toHom_iff
#print axioms Module.Germ.Pair.toHom_surjective
#print axioms Module.Germ.Pair.toHom_ofLinearMap
#print axioms twice_epic_one_not_zero
#print axioms twice_germ_ne_zero
#print axioms half_twice
#print axioms dense_even_preimage
#print axioms infinite_sum_locSmall
#print axioms finite_target_zero_germ
#print axioms composition_order
#print axioms finite_pair_target_enlargement

end AlgebraicAnalysisTest.Germ
