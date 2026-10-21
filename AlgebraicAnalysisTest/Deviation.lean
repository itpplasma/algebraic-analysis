module
public import AlgebraicAnalysis.Module.DeviationOmega
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

/-!
Concrete deviation oracles. Finite-dimensional vector spaces have deviation
zero regardless of their finite chain length. The integer module has bound
one but not zero: its nonzero quotients are finite, while an Artinian domain
would be a field. These checks use independent Mathlib finiteness/field APIs.
-/

namespace AlgebraicAnalysisTest.Deviation

open scoped DirectSum

theorem finiteDimensional_devLE_zero (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] : Module.DevLE K 0 V := by
  exact Module.devLE_zero_iff_isArtinian.mpr inferInstance

example : Module.DevLE ℚ 0 (Fin 2 → ℚ) := finiteDimensional_devLE_zero _ _

/-- A nonzero vector space is Artinian without belonging to stratum zero. -/
example : Module.Small ℚ 1 ℚ ∧ ¬Module.Small ℚ 0 ℚ := by
  refine ⟨finiteDimensional_devLE_zero _ _, fun h => ?_⟩
  exact zero_ne_one (h.elim 0 1)

private theorem int_quotient_finite (B : Submodule ℤ ℤ) (hB : B ≠ ⊥) :
    Finite (ℤ ⧸ B) := by
  let z := Submodule.IsPrincipal.generator (B : Ideal ℤ)
  have hz : z ≠ 0 := fun h => hB
    ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero B).mpr h)
  let : NeZero z := ⟨hz⟩
  have he : Ideal.span ({z} : Set ℤ) = B := Ideal.span_singleton_generator B
  rw [← he]
  infer_instance

/-- All nonzero successive lower terms give finite quotient intervals. -/
theorem int_devLE_one : Module.DevLE ℤ 1 ℤ := by
  intro c hc
  by_cases hz : ∃ N, c N = ⊥
  · obtain ⟨N, hN⟩ := hz
    refine ⟨N, fun i hi => ?_⟩
    have he : c i = ⊥ := le_bot_iff.mp (hN ▸ hc hi)
    have he' : c (i + 1) = ⊥ := le_bot_iff.mp
      (hN ▸ hc (Nat.le_trans hi (Nat.le_succ i)))
    rw [he, he']
    exact Order.devLE_of_subsingleton 0
  · push Not at hz
    refine ⟨0, fun i _ => ?_⟩
    have : Finite (ℤ ⧸ c (i + 1)) := int_quotient_finite _ (hz _)
    have hq : Module.DevLE ℤ 0 (ℤ ⧸ c (i + 1)) :=
      Module.devLE_zero_iff_isArtinian.mpr isArtinian_of_finite
    have hI := (Order.devLE_orderIso_iff 0 (Submodule.comapMkQRelIso (c (i + 1)))).mp hq
    exact hI.of_strictMono
      (f := fun U : Set.Icc (c (i + 1)) (c i) =>
        (⟨U.val, U.property.1⟩ : Set.Ici (c (i + 1)))) (fun _ _ h => h)

/-- The Artinian bound would force the integer domain to be a field. -/
theorem int_not_devLE_zero : ¬Module.DevLE ℤ 0 ℤ := by
  intro h
  have : IsArtinianRing ℤ := Module.devLE_zero_iff_isArtinian.mp h
  exact Int.not_isField (IsArtinianRing.isField_of_isDomain ℤ)

example : Module.Small ℤ 2 (ℤ × ℤ) := int_devLE_one.prod int_devLE_one

example : Module.DevLE ℤ 1 (Fin 3 → ℤ) := Module.DevLE.pi fun _ => int_devLE_one

example : Module.DevLE ℤ 1 (Fin 3 → ℤ) := int_devLE_one.of_finite

example : Module.DevLE ℤ 1 (⨁ _ : Fin 3, ℤ) := Module.DevLE.directSum fun _ => int_devLE_one

example (p : Submodule ℤ ℤ) :
    Module.DevLE ℤ 1 p ∧ Module.DevLE ℤ 1 (ℤ ⧸ p) :=
  (Module.devLE_iff_of_exact 1 p.subtype p.mkQ Subtype.val_injective
    (Submodule.mkQ_surjective p) (LinearMap.exact_subtype_mkQ p)).mp int_devLE_one

example : Module.DevLE ℤ 0 (ℤ ⧸ (Ideal.span ({6} : Set ℤ))) :=
  Module.devLE_zero_iff_isArtinian.mpr isArtinian_of_finite

example : Module.DevLE ℤ 1 (ℤ × ℤ) ∧ ¬Module.DevLE ℤ 0 (ℤ × ℤ) := by
  refine ⟨int_devLE_one.prod int_devLE_one, fun h => int_not_devLE_zero ?_⟩
  exact h.of_surjective (LinearMap.fst ℤ ℤ ℤ) LinearMap.fst_surjective

/-- Multiplication by two drops the integer module to a nonzero Artinian quotient. -/
theorem int_mul_two_quotient :
    Module.DevLE ℤ 0 (ℤ ⧸ LinearMap.range (LinearMap.mulLeft ℤ (2 : ℤ))) ∧
      ¬Subsingleton (ℤ ⧸ LinearMap.range (LinearMap.mulLeft ℤ (2 : ℤ))) := by
  refine ⟨int_devLE_one.quotient_range_of_injective (LinearMap.mulLeft ℤ (2 : ℤ))
    (fun _ _ h => mul_left_cancel₀ (by norm_num) h), fun h => ?_⟩
  have ht := Submodule.Quotient.subsingleton_iff.mp h
  have hm : (1 : ℤ) ∈ LinearMap.range (LinearMap.mulLeft ℤ (2 : ℤ)) := ht ▸ Submodule.mem_top
  obtain ⟨x, hx⟩ := hm
  change 2 * x = 1 at hx
  omega

example : ∃ n, Module.DevLE ℤ n
    (ℤ ⧸ LinearMap.range (LinearMap.mulLeft ℤ (2 : ℤ))) :=
  int_devLE_one.omega.quotient_range_of_injective (LinearMap.mulLeft ℤ (2 : ℤ))
    (fun _ _ h => mul_left_cancel₀ (by norm_num) h)

#print axioms Order.DevLE.of_strictMono
#print axioms Order.devLE_orderIso_iff
#print axioms Order.DevLE.mono
#print axioms Order.DevLE.prod
#print axioms Module.devLE_zero_iff_isArtinian
#print axioms Module.devLE_iff_submodule_quotient
#print axioms Module.small_iff_submodule_quotient
#print axioms Module.devLE_iff_of_exact
#print axioms Module.small_iff_of_exact
#print axioms Module.devLE_succ_iff
#print axioms Module.DevLE.pi
#print axioms Module.Small.pi
#print axioms Module.DevLE.directSum
#print axioms Module.Small.directSum
#print axioms Module.DevLE.of_finite
#print axioms Submodule.quotientIntervalOrderIso
#print axioms Submodule.devLE_interval_iff
#print axioms finiteDimensional_devLE_zero
#print axioms int_devLE_one
#print axioms int_not_devLE_zero
#print axioms Module.DevLE.omega
#print axioms Module.quotientRangePowOrderIso
#print axioms Module.DevLE.quotient_range_of_injective
#print axioms Module.DevLEOmega.quotient_range_of_injective
#print axioms Module.Small.quotient_range_of_injective
#print axioms Module.principalRightPowOrderIso
#print axioms Module.Small.principal_right_quotient
#print axioms Module.DevLEOmega.principal_right_quotient
#print axioms int_mul_two_quotient

end AlgebraicAnalysisTest.Deviation
