import AlgebraicAnalysis.Module.FilteredTwoTermBoundaryNaturality
import AlgebraicAnalysis.Module.FilteredTwoTermSuccessorNaturality
import AlgebraicAnalysis.Module.CommutingPolynomialAction

/-! A concrete filtered zero differential and identity page action consumer. -/

open AlgebraicAnalysis.FilteredTwoTermPages

namespace FilteredTwoTermPublication

noncomputable section

def stepFiltration : ℤ → Submodule ℚ ℚ :=
  fun p => if p ≤ 0 then ⊤ else ⊥

def zeroComplex : FilteredTwoTerm ℚ ℚ where
  G := stepFiltration
  antitone := by
    intro p q hpq
    by_cases hq : q ≤ 0
    · have hp : p ≤ 0 := hpq.trans hq
      simp [stepFiltration, hp, hq]
    · by_cases hp : p ≤ 0 <;> simp [stepFiltration, hp, hq]
  f := 0
  map_le := by
    intro p
    simp

def identityOperator : zeroComplex.PageOperator 0 where
  g := LinearMap.id
  commute := by
    apply LinearMap.ext
    intro x
    simp [zeroComplex]
  shift := by
    intro p x hx
    simpa using hx

def sourceRepresentative : zeroComplex.cycles 0 0 :=
  ⟨1, by simp [FilteredTwoTerm.cycles, zeroComplex, stepFiltration]⟩

def targetRepresentative : zeroComplex.G 0 :=
  ⟨1, by simp [zeroComplex, stepFiltration]⟩

example :
    zeroComplex.drop 0 0 (Submodule.Quotient.mk sourceRepresentative) = 0 := by
  rw [zeroComplex.drop_mk]
  rw [Submodule.Quotient.mk_eq_zero]
  change (0 : ℚ) ∈ zeroComplex.boundaries 0 0
  simp [FilteredTwoTerm.boundaries, zeroComplex, stepFiltration]

example :
    zeroComplex.targetBoundaryMap 0 0
        (Submodule.Quotient.mk targetRepresentative) =
      Submodule.Quotient.mk targetRepresentative := by
  rw [zeroComplex.targetBoundaryMap_mk]

example :
    identityOperator.targetMap 0 0
        (Submodule.Quotient.mk targetRepresentative) =
      Submodule.Quotient.mk targetRepresentative := by
  rw [identityOperator.targetMap_mk]
  rfl

example :
    identityOperator.targetMapAtDrop 0 0
        (zeroComplex.drop 0 0 (Submodule.Quotient.mk sourceRepresentative)) =
      zeroComplex.drop 0 0
        (identityOperator.sourceMap 0 0
          (Submodule.Quotient.mk sourceRepresentative)) := by
  exact identityOperator.targetMapAtDrop_drop 0 0 _

example :
    AlgebraicAnalysis.CommutingPolynomialAction.commutingPolynomialAction
        (fun _ : Unit => (1 : Module.End ℚ ℚ))
        (by intro _ _; simp)
        (MvPolynomial.X ()) = (1 : Module.End ℚ ℚ) := by
  simp

end

end FilteredTwoTermPublication
