import AlgebraicAnalysis.Ore.Associativity
import AlgebraicAnalysis.Ore.RightPBW
import AlgebraicAnalysis.Ore.RightQuotient
import AlgebraicAnalysis.Ore.IteratedTower
import AlgebraicAnalysis.Module.SplitLatticePresentation
import AlgebraicAnalysis.Module.FilteredTwoTermPageEquivalences
import AlgebraicAnalysis.FieldTheory.FunctionField
import AlgebraicAnalysis.Polynomial.DistinguishedVariable
import AlgebraicAnalysis.Module.CommutingPolynomialAction
import AlgebraicAnalysis.Module.PrincipalKoszulSupportOverBase
import AlgebraicAnalysis.Module.StableTorsionResidualSupport
import AlgebraicAnalysis.Module.LocalizedMinimalSupportAvoidance
import AlgebraicAnalysis.Module.MinimalPrimeFiniteLengthLocalization
import AlgebraicAnalysis.Module.MinimalSupportExistence
import AlgebraicAnalysis.RingTheory.BinomialSeriesRoot
import AlgebraicAnalysis.RingTheory.RatFuncAtInfinity
import AlgebraicAnalysis.RingTheory.RatFuncAtPoint

#print axioms AlgebraicAnalysis.OreAssociativity.rightMul_assoc_of_ring
#print axioms AlgebraicAnalysis.OreRightPBW.rightOrePBWBasis
#print axioms AlgebraicAnalysis.OreRightQuotient.twoGeneratorQuotient_finite
#print axioms AlgebraicAnalysis.OreIteratedTower.build
#print axioms AlgebraicAnalysis.OreIteratedTower.iteratedNormalForm
#print axioms AlgebraicAnalysis.SplitLatticePresentation.exists_splitMatrixPresentation
#print axioms AlgebraicAnalysis.FilteredTwoTermPages.FilteredTwoTerm.sourceSuccEquivKerDrop
#print axioms AlgebraicAnalysis.FilteredTwoTermPages.FilteredTwoTerm.targetSuccEquivCokerDrop
#print axioms AlgebraicAnalysis.FunctionField.top_fg_of_finiteType_fractionRing
#print axioms AlgebraicAnalysis.MvPolynomial.X_mem_of_homogeneous_mem_prime
#print axioms PowerSeries.subst_binomialSeries_div_pow
#print axioms RatFunc.coeff_atInfinity_algebraMap
#print axioms RatFunc.residueAtPoint_derivative
#print axioms AlgebraicAnalysis.PrincipalKoszulSupportOverBase.length_cokernel_gt_kernel_of_support_over_base
#print axioms AlgebraicAnalysis.StableTorsionResidualSupport.residual_nontrivial_of_support
#print axioms AlgebraicAnalysis.LocalizedMinimalSupportAvoidance.localized_minimalPrime_avoids
#print axioms AlgebraicAnalysis.MinimalPrimeFiniteLengthLocalization.localizedModule_nontrivial_and_isFiniteLength
#print axioms AlgebraicAnalysis.MinimalSupportExistence.exists_minimal_support_prime

open scoped PowerSeries

-- Independent concrete checks on the two series ports used by Stafford-style
-- local expansions: a fractional binomial square and polynomial coefficients at infinity.
example :
    ((PowerSeries.binomialSeries ℚ ((1 : ℚ) / (2 : ℚ))).subst PowerSeries.X) ^ 2 =
      (1 + PowerSeries.X : PowerSeries ℚ) ^ 1 := by
  exact PowerSeries.subst_binomialSeries_div_pow
    PowerSeries.X (PowerSeries.constantCoeff_X (R := ℚ)) 1 2 (by decide)

noncomputable def samplePolynomialAtInfinity : Polynomial ℚ :=
  (Polynomial.X : Polynomial ℚ) ^ 2 +
    Polynomial.C (2 : ℚ) * Polynomial.X + Polynomial.C (3 : ℚ)

example :
    (RatFunc.atInfinity ℚ
      (algebraMap (Polynomial ℚ) (RatFunc ℚ) samplePolynomialAtInfinity)).coeff (-1) =
        (2 : ℚ) := by
  simpa [samplePolynomialAtInfinity] using
    (RatFunc.coeff_atInfinity_algebraMap ℚ samplePolynomialAtInfinity 1)

example (a : ℚ) (f : RatFunc ℚ) :
    RatFunc.residueAtPoint ℚ a (RatFunc.derivative ℚ f) = 0 :=
  RatFunc.residueAtPoint_derivative ℚ a f

example :
    AlgebraicAnalysis.CommutingPolynomialAction.commutingPolynomialAction
      (fun _ : Unit => (LinearMap.id : ℚ →ₗ[ℚ] ℚ))
      (by intro _i _j; rfl) (MvPolynomial.X ()) = LinearMap.id := by
  exact
    (AlgebraicAnalysis.CommutingPolynomialAction.commutingPolynomialAction_apply_X
      (fun _ : Unit => (LinearMap.id : ℚ →ₗ[ℚ] ℚ))
      (by intro _i _j; rfl) ())

example : Nonempty (AlgebraicAnalysis.SplitLatticePresentation.SplitMatrixPresentation
    (⊤ : Submodule ℚ (Fin 2 → ℚ)) 2) := by
  apply AlgebraicAnalysis.SplitLatticePresentation.exists_splitMatrixPresentation
    (L := ⊤) (L' := ⊥) isCompl_top_bot 2
  rw [finrank_top, Module.finrank_pi]
  norm_num

example : RatFunc.residueAtPoint ℚ 0
    ((algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X)⁻¹ ^ 2) = 0 := by
  have h := RatFunc.residueAtPoint_inverse_sq_algebraMap
    (K := ℚ) (M := Polynomial.X) (a := 0) (by simp) (by simp)
  simpa using h
