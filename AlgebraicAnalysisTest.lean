import AlgebraicAnalysis

/-! Small API consumer for the first extracted Ore slice. -/

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity

def zeroDerivation : OreDivisionDerivation ℚ where
  toFun := fun _ => 0
  map_zero' := by simp
  map_add' := by intro a b; simp
  leibniz' := by intro a b; simp

example (p q r : Polynomial ℚ) :
    rightMul zeroDerivation (rightMul zeroDerivation p q) r =
      rightMul zeroDerivation p (rightMul zeroDerivation q r) := by
  exact rightMul_assoc_of_ring zeroDerivation p q r
