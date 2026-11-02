/- SPDX-License-Identifier: Apache-2.0 -/

module
public import AlgebraicAnalysis.Filtration.SymbolPresentation
public import AlgebraicAnalysisTest.Filtration.SymbolNoetherian

@[expose] public section

/-!
Oracles for surjective symbol presentations.

* Self-presentation: the degree filtration of `ℚ[X₀, X₁]` is presented by its own
  degree symbol `S₂`, through `GradedSymbol.toPresentation`. Its presentation class
  of a homogeneous `X₀` in degree one is the class of `X₀` (checked against the
  explicit symbol `X₀` of `X₀`, not against the presentation machinery).
* Noetherian oracle: the presentation's conclusion `IsNoetherianRing ℚ[X₀, X₁]` is
  Hilbert's basis theorem, Mathlib's instance, which the presentation must agree with.
-/

namespace AlgebraicAnalysisTest.SymbolPresentation

open AlgebraicAnalysis AlgebraicAnalysis.RingFiltration MvPolynomial DirectSum
open AlgebraicAnalysisTest.SymbolNoetherian

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The identity presentation of the degree filtration of `ℚ[X₀, X₁]`. -/
noncomputable abbrev P₂ := S₂.toPresentation

/-- Membership of `X₀` in degree `1` of the degree filtration. -/
theorem X0_mem_F1 : (X 0 : MvPolynomial (Fin 2) ℚ) ∈
    (RingFiltration.ofGradedAlgebra (homogeneousSubmodule (Fin 2) ℚ)).F 1 :=
  mem_degreeLE_of_mem ((mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℚ 0))

/-- The presentation class of `X₀` in degree one is the class of `X₀ ∈ F₁`. -/
theorem P₂_sym_X0 :
    P₂.sym 1 ⟨X 0, (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℚ 0)⟩ =
      Submodule.Quotient.mk ⟨X 0, X0_mem_F1⟩ := by
  change (S₂.gradedQuotientEquiv 1).symm _ = _
  rw [LinearEquiv.symm_apply_eq, GradedSymbol.gradedQuotientEquiv_mk]
  apply Subtype.ext
  change (X 0 : MvPolynomial (Fin 2) ℚ) =
    (decompose (homogeneousSubmodule (Fin 2) ℚ) (X 0) 1 : MvPolynomial (Fin 2) ℚ)
  rw [decompose_of_mem_same _ ((mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℚ 0))]

/-- Hilbert's basis theorem, through the presentation: `ℚ[X₀, X₁]` is Noetherian on
both sides. -/
example : IsNoetherianRing (MvPolynomial (Fin 2) ℚ) := P₂.isNoetherianRing

/-- The right side is Noetherian as well, by the same presentation. -/
example : IsNoetherian (MvPolynomial (Fin 2) ℚ)ᵐᵒᵖ (MvPolynomial (Fin 2) ℚ) :=
  P₂.isNoetherian_right

#print axioms P₂_sym_X0
