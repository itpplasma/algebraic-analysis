import AlgebraicAnalysis.Module.SplitLatticePresentation

/-!
# Concrete consumer for split lattice presentations

The full coordinate module over `ℚ` is complemented by the zero submodule.
The exported construction therefore produces a two-column matrix and a
retraction matrix whose product is the identity and whose columns span the
whole module.
-/

open AlgebraicAnalysis.SplitLatticePresentation

namespace SplitLatticePresentation

noncomputable section

abbrev Coordinates := Fin 2 → ℚ

def full : Submodule ℚ Coordinates := ⊤

example :
    ∃ P : SplitMatrixPresentation full 2,
      (P.C * P.B = 1 ∧
        Submodule.span ℚ (Set.range fun j => fun i => P.B i j) = full) := by
  have hrank : Module.finrank ℚ full = 2 := by
    change Module.finrank ℚ (⊤ : Submodule ℚ (Fin 2 → ℚ)) = 2
    rw [finrank_top]
    exact Module.finrank_pi ℚ
  obtain ⟨P⟩ := exists_splitMatrixPresentation full ⊥
    isCompl_top_bot 2 hrank
  exact ⟨P, P.leftInverse, P.columnsSpan⟩

example :
    Nonempty (SplitMatrixPresentation full 2) := by
  apply exists_splitMatrixPresentation_of_isComplemented
  exact ⟨⊥, isCompl_top_bot⟩
  change Module.finrank ℚ (⊤ : Submodule ℚ (Fin 2 → ℚ)) = 2
  rw [finrank_top]
  exact Module.finrank_pi ℚ

end

end SplitLatticePresentation
