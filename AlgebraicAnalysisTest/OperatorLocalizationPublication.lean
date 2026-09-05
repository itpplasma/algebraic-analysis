import AlgebraicAnalysis.LinearAlgebra.FiniteTaylorReconstruction
import AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration
import AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations
import AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialCommutant
import AlgebraicAnalysis.Ore.RightLocalization
import AlgebraicAnalysis.RingTheory.TwoGeneratorIdentity

/-!
# Independent operator and localization consumers

These examples exercise the extracted interfaces through concrete finite
Taylor and denominator calculations.  They do not inspect the extraction
patch or rely on Stafford-specific declarations.
-/

open AlgebraicAnalysis
open AlgebraicAnalysis.FiniteTaylorReconstruction
open AlgebraicAnalysis.DifferentialOperators
open AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations
open AlgebraicAnalysis.OreRightLocalization

namespace OperatorLocalizationPublication

noncomputable section

example {V : Type*} [AddCommGroup V] [Module ℚ V] (x : V) :
    x = ∑ j ∈ Finset.range (0 + 1),
      ((1 : ℚ) / (j.factorial : ℚ)) •
        ((0 ^ j * projectorMapG (𝕜 := ℚ) 0 0 0 * 0 ^ j) x) := by
  exact reconstruction_all (𝕜 := ℚ) 0 0 0 x (by simp)

example {V : Type*} [AddCommGroup V] [Module ℚ V]
    (S D : V →ₗ[ℚ] V) (x : V) (hD : D x = 0) :
    x = ∑ j ∈ Finset.range (0 + 1),
      ((1 : ℚ) / (j.factorial : ℚ)) •
        ((S ^ j * projectorMapG (𝕜 := ℚ) 0 S D * D ^ j) x) := by
  exact reconstruction_all (𝕜 := ℚ) 0 S D x (by simpa [pow_one] using hD)

example {R : Type*} [Ring R] (d : R) (hd : IsUnit d) :
    ∃ F r s : R, (1 : R) = d * r + F * d * s := by
  refine ⟨0, (↑(hd.unit⁻¹) : R), 0, ?_⟩
  have h : d * (↑(hd.unit⁻¹) : R) = 1 := by
    simpa [hd.unit_spec] using hd.unit.val_inv
  simp [h]

example :
    TwoGeneratorIdentity (OreRightLocalization.RightOreLocalization ℚ (⊤ : Submonoid ℚ)) := by
  apply TwoGeneratorIdentity.of_rightOreLocalization
  intro d hd
  refine ⟨0, d⁻¹, 0, ?_⟩
  simp [hd]

example {n : ℕ} (S : Submonoid (MvPolynomial (Fin n) ℚ))
    (B : Type) [CommRing B]
    [Algebra (MvPolynomial (Fin n) ℚ) B] [Algebra ℚ B]
    [IsScalarTower ℚ (MvPolynomial (Fin n) ℚ) B]
    [IsLocalization S B] (i j : Fin n) :
    localizedPderiv S B i
        (algebraMap (MvPolynomial (Fin n) ℚ) B (MvPolynomial.X j)) =
      if i = j then 1 else 0 :=
  localizedPderiv_apply_algebraMap_X S B i j

end

end OperatorLocalizationPublication
