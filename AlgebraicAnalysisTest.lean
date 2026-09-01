import AlgebraicAnalysis

/-! Small API consumer for the first extracted Ore slice. -/

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreLeftPBW
open AlgebraicAnalysis.OreRightPBW
open AlgebraicAnalysis.OreTower
open AlgebraicAnalysis.OreIteratedTower
open AlgebraicAnalysis.OreIteratedPBW

noncomputable section

example {A : Type*} [Ring A] (u v x : A) :
    AlgebraicAnalysis.ringCommutator (u * v) x =
      u * AlgebraicAnalysis.ringCommutator v x +
        AlgebraicAnalysis.ringCommutator u x * v := by
  exact AlgebraicAnalysis.ringCommutator_mul u v x

example {A : Type*} [Ring A] (z x : A)
    (h : AlgebraicAnalysis.ringCommutator z x = 1) :
    AlgebraicAnalysis.ringCommutator (z ^ 3) x = 3 • z ^ 2 := by
  simpa using AlgebraicAnalysis.ringCommutator_pow z x h 3

def zeroDerivation : OreDivisionDerivation ℚ where
  toFun := fun _ => 0
  map_zero' := by simp
  map_add' := by intro a b; simp
  leibniz' := by intro a b; simp

example (p q r : Polynomial ℚ) :
    rightMul zeroDerivation (rightMul zeroDerivation p q) r =
      rightMul zeroDerivation p (rightMul zeroDerivation q r) := by
  exact rightMul_assoc_of_ring zeroDerivation p q r

example (D : OreDivisionDerivation ℚ) (n : ℕ) :
    orePBWBasis D n = normalVariable D ^ n := by
  exact orePBWBasis_apply D n

example (D : OreDivisionDerivation ℚ) (n : ℕ) :
    rightOrePBWBasis D n = rightPBWMonomial D n := by
  exact rightOrePBWBasis_apply D n

example (Ds : List (Derivation ℚ)) (hDs : PairwiseCommutes Ds) :
    Function.Injective (iteratedNormalForm Ds hDs) := by
  exact iteratedNormalForm_injective Ds hDs

example (Ds : List (KDerivation ℚ)) (hDs : PairwiseCommutes Ds) :
    Basis (exponentIndex Ds) ℚ (OreTower Ds hDs) := by
  exact towerPBWBasis Ds hDs

end
