module
public import AlgebraicAnalysis.Filtration.SymbolNoetherian
public import AlgebraicAnalysisTest.Deviation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.KrullDimension.Field

@[expose] public section

/-!
Oracles for the Krull-dimension bound on deviation and for filtered rings
with commutative Noetherian associated graded ring.

* Commutative bound: `ringKrullDim ℤ = 1` (Mathlib, PID theory) yields
  `Module.DevLE ℤ 1 ℤ`, agreeing with the direct finite-quotient proof
  `AlgebraicAnalysisTest.Deviation.int_devLE_one`; the bound is sharp by the
  independent `int_not_devLE_zero`.
* Symbol data: the degree filtration of `ℚ[X₀, X₁]` (Mathlib's homogeneous
  grading) is a valid `GradedSymbol`; its degree-one symbol of `X₀ + 1` is
  `X₀` and of `1` is zero, checked against Mathlib's homogeneity API.
* Filtered consequences: the conclusions agree with Mathlib's Hilbert basis
  instance, and for `ℚ[X]` (Krull dimension one) the deviation bound one is
  sharp because `ℚ[X]` is not Artinian.
-/

namespace AlgebraicAnalysisTest.SymbolNoetherian

open AlgebraicAnalysis AlgebraicAnalysis.RingFiltration MvPolynomial DirectSum

/-! ## The commutative bound -/

theorem int_ringKrullDim : ringKrullDim ℤ = 1 :=
  IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

example : Module.DevLE ℤ 1 ℤ :=
  Module.devLE_of_ringKrullDim_le 1 (by rw [int_ringKrullDim]; rfl)

/-- The Krull bound is sharp for `ℤ`: deviation one but not zero. -/
example : Module.DevLE ℤ 1 ℤ ∧ ¬Module.DevLE ℤ 0 ℤ :=
  ⟨Module.devLE_of_ringKrullDim_le 1 (by rw [int_ringKrullDim]; rfl),
    AlgebraicAnalysisTest.Deviation.int_not_devLE_zero⟩

/-- A field has Krull dimension zero, hence is Artinian. -/
example : IsArtinianRing ℚ :=
  Module.devLE_zero_iff_isArtinian.mp
    (Module.devLE_of_ringKrullDim_le 0 (by rw [ringKrullDim_eq_zero_of_field ℚ]; rfl))

/-! ## Symbol data for the degree filtration of a polynomial ring -/

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The symbol data of the degree filtration of `ℚ[X₀, X₁]`. -/
noncomputable abbrev S₂ :=
  GradedSymbol.ofGradedAlgebra (homogeneousSubmodule (Fin 2) ℚ)

theorem X_add_one_mem : (X 0 + 1 : MvPolynomial (Fin 2) ℚ) ∈
    (RingFiltration.ofGradedAlgebra (homogeneousSubmodule (Fin 2) ℚ)).F 1 := by
  refine Submodule.add_mem _ (mem_degreeLE_of_mem ?_)
    ((RingFiltration.ofGradedAlgebra _).mono (Nat.zero_le 1)
      (RingFiltration.ofGradedAlgebra _).one_mem)
  exact (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℚ 0)

/-- Degree-one symbol of `X₀ + 1` is `X₀`. -/
example : S₂.grAt 1 (X 0 + 1 : MvPolynomial (Fin 2) ℚ) = X 0 := by
  rw [GradedSymbol.grAt_of_mem _ X_add_one_mem]
  change (decompose (homogeneousSubmodule (Fin 2) ℚ) (X 0 + 1) 1 : MvPolynomial (Fin 2) ℚ) = _
  rw [decompose_add, DirectSum.add_apply, Submodule.coe_add,
    decompose_of_mem_same _ ((mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℚ 0)),
    decompose_of_mem_ne _ ((mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_one _ ℚ))
      (by norm_num), add_zero]

/-- The constant `1` has zero symbol in degree one but symbol `1` in degree zero. -/
example : S₂.grAt 1 (1 : MvPolynomial (Fin 2) ℚ) = 0 ∧
    S₂.grAt 0 (1 : MvPolynomial (Fin 2) ℚ) = 1 := by
  have h1 : (1 : MvPolynomial (Fin 2) ℚ) ∈ homogeneousSubmodule (Fin 2) ℚ 0 :=
    (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_one _ ℚ)
  have hF : ∀ n, (1 : MvPolynomial (Fin 2) ℚ) ∈
      (RingFiltration.ofGradedAlgebra (homogeneousSubmodule (Fin 2) ℚ)).F n :=
    fun n => (RingFiltration.ofGradedAlgebra _).mono (Nat.zero_le n)
      (RingFiltration.ofGradedAlgebra _).one_mem
  constructor
  · rw [GradedSymbol.grAt_of_mem _ (hF 1)]
    exact decompose_of_mem_ne _ h1 (by norm_num)
  · rw [GradedSymbol.grAt_of_mem _ (hF 0)]
    exact decompose_of_mem_same _ h1

/-! ## Filtered consequences -/

/-- Right Noetherianity of `ℚ[X₀, X₁]` from its symbol data. -/
example : IsNoetherian (MvPolynomial (Fin 2) ℚ)ᵐᵒᵖ (MvPolynomial (Fin 2) ℚ) :=
  S₂.isNoetherian_right

/-- Left Noetherianity from the symbol data agrees with Mathlib's Hilbert
basis instance. -/
example : S₂.isNoetherianRing = (inferInstance : IsNoetherianRing (MvPolynomial (Fin 2) ℚ)) :=
  rfl

theorem pUnit_ringKrullDim : ringKrullDim (MvPolynomial PUnit ℚ) = 1 := by
  rw [ringKrullDim_eq_of_ringEquiv (uniqueAlgEquiv ℚ PUnit).toRingEquiv]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one _ (Polynomial.not_isField ℚ)

/-- `ℚ[X]` with its degree filtration: deviation at most one on both sides. -/
example : Module.DevLE (MvPolynomial PUnit ℚ)ᵐᵒᵖ 1 (MvPolynomial PUnit ℚ) ∧
    Module.DevLE (MvPolynomial PUnit ℚ) 1 (MvPolynomial PUnit ℚ) :=
  ⟨(GradedSymbol.ofGradedAlgebra (homogeneousSubmodule PUnit ℚ)).devLE_right 1
      (by rw [pUnit_ringKrullDim]; rfl),
    (GradedSymbol.ofGradedAlgebra (homogeneousSubmodule PUnit ℚ)).devLE_left 1
      (by rw [pUnit_ringKrullDim]; rfl)⟩

/-- Sharpness: `ℚ[X]` is not Artinian, so its deviation is not zero. -/
example : ¬Module.DevLE (MvPolynomial PUnit ℚ) 0 (MvPolynomial PUnit ℚ) := by
  intro h
  have : IsArtinianRing (MvPolynomial PUnit ℚ) := Module.devLE_zero_iff_isArtinian.mp h
  have hf := IsArtinianRing.isField_of_isDomain (MvPolynomial PUnit ℚ)
  exact Polynomial.not_isField ℚ
    (MulEquiv.isField hf (uniqueAlgEquiv ℚ PUnit).toMulEquiv.symm)

/-- Deviation at most omega on the right, the form used by downstream consumers. -/
example : Module.DevLEOmega (MvPolynomial PUnit ℚ)ᵐᵒᵖ (MvPolynomial PUnit ℚ) :=
  (GradedSymbol.ofGradedAlgebra (homogeneousSubmodule PUnit ℚ)).devLEOmega_right
    (by rw [pUnit_ringKrullDim]; decide)

#print axioms Module.devLE_of_ringKrullDim_le
#print axioms Module.small_of_le_annihilator
#print axioms Module.small_quotient_prime_of_coheight_lt
#print axioms GradedSymbol.ofGradedAlgebra
#print axioms GradedSymbol.eq_of_le_of_grSpan_le
#print axioms GradedSymbol.isNoetherian_right
#print axioms GradedSymbol.isNoetherianRing
#print axioms GradedSymbol.devLE_right
#print axioms GradedSymbol.devLE_left
#print axioms GradedSymbol.devLEOmega_right
#print axioms GradedSymbol.devLEOmega_left

end AlgebraicAnalysisTest.SymbolNoetherian
