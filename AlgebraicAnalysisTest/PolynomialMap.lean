import AlgebraicAnalysis.HessianAlgebra.AffineInverse
import AlgebraicAnalysis.HessianAlgebra.ConstantHessian
import AlgebraicAnalysis.HessianAlgebra.CoordinateChange
import AlgebraicAnalysis.HessianAlgebra.DerivativeKernel
import AlgebraicAnalysis.HessianAlgebra.HessianCoordinateChange
import AlgebraicAnalysis.HessianAlgebra.HomogeneousDifferential
import AlgebraicAnalysis.HessianAlgebra.HomogeneousSubstitution
import AlgebraicAnalysis.HessianAlgebra.HomogeneousSupport
import AlgebraicAnalysis.HessianAlgebra.PolynomialMap
import AlgebraicAnalysis.HessianAlgebra.TriangularInverse

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

example : (C 7 : P) = C (coeff 0 (C 7 : P)) := by
  exact HessianAlgebra.eq_constant_of_pderiv_eq_zero (C 7 : P) (by simp)

example : homogeneousComponent 2
    (substitute (fun i : Fin 2 => X i) (X 0 ^ 2 : P)) = X 0 ^ 2 := by
  rw [show substitute (fun i : Fin 2 => X i) (X 0 ^ 2 : P) = X 0 ^ 2 by
    simp [substitute]]
  exact homogeneousComponent_eq_self (isHomogeneous_X_pow 0 2)

end

end AlgebraicAnalysisTest.PolynomialMap
