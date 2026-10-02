module
public import AlgebraicAnalysis.HessianAlgebra.AffineInverse
public import AlgebraicAnalysis.HessianAlgebra.ConstantHessian
public import AlgebraicAnalysis.HessianAlgebra.CoordinateChange
public import AlgebraicAnalysis.HessianAlgebra.DerivativeKernel
public import AlgebraicAnalysis.HessianAlgebra.HessianCoordinateChange
public import AlgebraicAnalysis.HessianAlgebra.HomogeneousDifferential
public import AlgebraicAnalysis.HessianAlgebra.HomogeneousSubstitution
public import AlgebraicAnalysis.HessianAlgebra.HomogeneousSupport
public import AlgebraicAnalysis.HessianAlgebra.PolynomialMap
public import AlgebraicAnalysis.HessianAlgebra.TriangularInverse

@[expose] public section

/-!
Behavioral tests for the extracted polynomial-map API.  The expected values
are computed directly from concrete polynomials, independently of the source
repository text.
-/

namespace AlgebraicAnalysisTest.PolynomialMap

open MvPolynomial
open HessianAlgebra.PolynomialMap

noncomputable section

private abbrev P := MvPolynomial (Fin 2) ℚ
private abbrev M := Matrix (Fin 2) (Fin 2) ℚ

example : substitute (fun i : Fin 2 => X i + 1) (X 0 * X 1 : P) =
    (X 0 + 1) * (X 1 + 1) := by
  simp [substitute]

example : partialDerivative 0 (X 0 ^ 2 * X 1 : P) = 2 * X 0 * X 1 := by
  simp [partialDerivative]
  ring

example : hessian (X 0 * X 1 : P) 0 1 = 1 := by
  simp [hessian, partialDerivative]

example : affine (1 : M) 0 0 = (X 0 : P) := by
  simp [affine, Matrix.one_apply]

example : affineInverse (1 : M) 0 1 = (X 1 : P) := by
  simp [affineInverse, Matrix.one_apply]

example : (C 7 : P) = C ((C 7 : P).coeff 0) := by
  exact HessianAlgebra.eq_constant_of_pderiv_eq_zero (C 7 : P) (by simp)

example : homogeneousComponent 2
    (substitute (fun i : Fin 2 => X i) (X 0 ^ 2 : P)) = X 0 ^ 2 := by
  rw [show substitute (fun i : Fin 2 => X i) (X 0 ^ 2 : P) = X 0 ^ 2 by
    simp [substitute]]
  exact homogeneousComponent_eq_self (isHomogeneous_X_pow 0 2)

end

end AlgebraicAnalysisTest.PolynomialMap
