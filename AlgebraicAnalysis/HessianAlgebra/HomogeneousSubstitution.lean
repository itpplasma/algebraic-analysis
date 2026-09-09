/- SPDX-License-Identifier: Apache-2.0 -/
-- Modified by itpplasma/algebraic-analysis: package module path changed.

import AlgebraicAnalysis.HessianAlgebra.PolynomialMap
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Homogeneous components commute with substitutions by linear homogeneous maps. -/

noncomputable section

namespace HessianAlgebra

open MvPolynomial
open PolynomialMap

variable {K : Type*} {σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- Substitution by degree-one homogeneous polynomials preserves every
homogeneous component. -/
theorem homogeneousComponent_substitute (g : σ → MvPolynomial σ K)
    (hg : ∀ i, (g i).IsHomogeneous 1) (d : ℕ)
    (H : MvPolynomial σ K) :
    homogeneousComponent d (PolynomialMap.substitute g H) =
      PolynomialMap.substitute g (homogeneousComponent d H) := by
  induction H using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | monomial e r =>
      have he : (monomial e r).IsHomogeneous e.degree :=
        isHomogeneous_monomial r rfl
      have he' : (PolynomialMap.substitute g (monomial e r)).IsHomogeneous e.degree := by
        simpa [PolynomialMap.substitute] using
          he.eval₂ (MvPolynomial.C : K →+* MvPolynomial σ K) g
            (fun a => isHomogeneous_C _ _) hg
      rw [homogeneousComponent_of_mem he']
      rw [homogeneousComponent_of_mem he]
      split_ifs <;> simp [PolynomialMap.substitute, *]

end HessianAlgebra
