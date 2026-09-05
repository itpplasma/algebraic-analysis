import AlgebraicAnalysis.Module.BaseLocalizationModuleComparison
import AlgebraicAnalysis.Module.LocalizedKernelCokernelEquivalences
import AlgebraicAnalysis.Module.MonicAnnihilatorFinite
import AlgebraicAnalysis.Module.TwoTermPageLength

/-!
# Concrete consumers for localization and finite-module endpoints

These examples exercise the exported maps on an explicit localized integer
module and instantiate the finite polynomial-annihilator interface over a
field.  They test the endpoint behavior through concrete values rather than
checking the source text or the migration patch.
-/

open AlgebraicAnalysis
open Polynomial

namespace LocalizationLengthPublication

noncomputable section

def powersTwo : Submonoid ℤ := Submonoid.powers 2

def negation : ℤ →ₗ[ℤ] ℤ where
  toFun x := -x
  map_add' x y := by simp [add_comm]
  map_smul' a x := by simp

example (m : ℤ) (s : powersTwo) :
    LocalizedKernelCokernelEquivalences.localizedMap powersTwo negation
        (LocalizedModule.mk m s) =
      LocalizedModule.mk (-m) s := by
  rw [LocalizedKernelCokernelEquivalences.localizedMap_apply]
  simp [LocalizedModule.map_mk, negation]

example (m : ℤ) (s : powersTwo) :
    BaseLocalizationModuleComparison.localizedModuleComparison powersTwo
        (LocalizedModule.mk m s) =
      (LocalizedModule.mk m
        (BaseLocalizationModuleComparison.coefficientDenominator powersTwo s) :
          LocalizedModule
            (Algebra.algebraMapSubmonoid ℤ powersTwo) ℤ) := by
  exact BaseLocalizationModuleComparison.localizedModuleComparison_mk
    powersTwo m s

example {R E : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [Module R[X] E]
    [IsScalarTower R R[X] E] [Module.Finite R[X] E]
    (hkill : ∀ z : E, (X : R[X]) • z = 0) :
    Module.Finite R E := by
  exact MonicAnnihilatorFinite.finite_of_variable_annihilates hkill

example {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [IsNoetherian R M] (D : ℕ →o Submodule R M)
    (hD : ⨆ r, D r = ⊤) : ∃ N, D N = ⊤ := by
  exact TwoTermPageLength.exists_boundary_eq_top_of_iSup_eq_top D hD

end

end LocalizationLengthPublication
