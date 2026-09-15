/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations
import AlgebraicAnalysis.RingTheory.LaurentSeriesCoefficientDerivation
import AlgebraicAnalysis.RingTheory.LaurentSeriesResidue
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Rational functions at a finite point

This module expands a one-variable rational function in the local parameter
`s = X - a`.  It also equips the rational function field with the derivative
extending `Polynomial.derivative` and proves that local expansion commutes with
this derivative.  Consequently, the residue at every finite point of a
rational derivative vanishes.

## Provenance

The finite-point residue argument is extracted from `itpplasma/jc2` at
revision `4a7add6104d021c2f2f3b0e903f66d15096b56c9`, file
`research/general-pq-carry-20260911/finite-moment-coordinates-all-m.md`,
section 3, graph node `direct-finite-moment-coordinates-all-m`. The source
repository's license is not asserted here. Authorship of the mathematical
argument follows that repository's history (Christopher Albert); this file
supplies the Lean implementation. `RatFunc.atPoint`, `RatFunc.derivative`, and
`RatFunc.residueAtPoint_derivative` implement respectively the note's local
Laurent expansion, rational derivative, and zero-residue-of-a-derivative step.
The downstream consumer is `itpplasma/jc2-formal`'s finite-moment module.
-/

noncomputable section

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations

namespace RatFunc

variable (K : Type*) [Field K]

/-- Taylor-expand a polynomial at `a` and include it in the Laurent series
field. Thus the target variable is the local parameter `s = X - a`. -/
def polynomialAtPoint (a : K) : K[X] →ₐ[K] LaurentSeries K :=
  { toRingHom :=
      (algebraMap (PowerSeries K) (LaurentSeries K)).comp
        (Polynomial.coeToPowerSeries.ringHom.comp
          (Polynomial.taylorAlgHom a).toRingHom)
    commutes' := by
      intro c
      simp [HahnSeries.algebraMap_apply'] }

theorem polynomialAtPoint_eq_taylor (a : K) (p : K[X]) :
    polynomialAtPoint K a p =
      algebraMap (PowerSeries K) (LaurentSeries K)
        ((Polynomial.taylor a p : K[X]) : PowerSeries K) :=
  rfl

theorem polynomialAtPoint_injective (a : K) :
    Function.Injective (polynomialAtPoint K a) := by
  intro p q h
  apply Polynomial.taylor_injective a
  apply Polynomial.coe_injective K
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  exact h

@[simp]
theorem polynomialAtPoint_X (a : K) :
    polynomialAtPoint K a Polynomial.X =
      HahnSeries.C a + (HahnSeries.single 1 1 : LaurentSeries K) := by
  rw [polynomialAtPoint_eq_taylor]
  simp [Polynomial.taylor_apply, add_comm]

/-- Laurent expansion of a rational function at the finite point `a`, in the
local parameter `s = X - a`. -/
def atPoint (a : K) : K⟮X⟯ →ₐ[K] LaurentSeries K :=
  RatFunc.liftAlgHom (polynomialAtPoint K a)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (polynomialAtPoint_injective K a))

@[simp]
theorem atPoint_algebraMap (a : K) (p : K[X]) :
    atPoint K a (algebraMap K[X] K⟮X⟯ p) = polynomialAtPoint K a p := by
  change RatFunc.liftAlgHom (polynomialAtPoint K a) _
      (algebraMap K[X] K⟮X⟯ p) = polynomialAtPoint K a p
  have h := RatFunc.liftAlgHom_apply_div
    (polynomialAtPoint K a)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (polynomialAtPoint_injective K a)) p 1
  simpa using h

@[simp]
theorem atPoint_X (a : K) :
    atPoint K a RatFunc.X =
      HahnSeries.C a + (HahnSeries.single 1 1 : LaurentSeries K) := by
  rw [RatFunc.X, atPoint_algebraMap, polynomialAtPoint_X]

private theorem derivative_taylor (a : K) (p : K[X]) :
    (Polynomial.taylor a p).derivative = Polynomial.taylor a p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
      simp [Polynomial.taylor_monomial, Polynomial.derivative_monomial]
      rw [Polynomial.derivative_pow]
      simp
      ring

theorem derivative_polynomialAtPoint (a : K) (p : K[X]) :
    LaurentSeries.derivative K (polynomialAtPoint K a p) =
      polynomialAtPoint K a p.derivative := by
  rw [polynomialAtPoint_eq_taylor, polynomialAtPoint_eq_taylor,
    show algebraMap (PowerSeries K) (LaurentSeries K) =
      HahnSeries.ofPowerSeries ℤ K by ext; rfl,
    LaurentSeries.derivative_ofPowerSeries, PowerSeries.derivative_coe,
    derivative_taylor]

/-- The derivation of the rational function field extending the ordinary
polynomial derivative. -/
def derivative : Derivation K K⟮X⟯ K⟮X⟯ :=
  extendDerivation K K[X] K⟮X⟯ (nonZeroDivisors K[X])
    ((Algebra.linearMap K[X] K⟮X⟯).compDer
      (Polynomial.derivative' : Derivation K K[X] K[X]))

@[simp]
theorem derivative_algebraMap (p : K[X]) :
    derivative K (algebraMap K[X] K⟮X⟯ p) =
      algebraMap K[X] K⟮X⟯ p.derivative := by
  have h := Derivation.congr_fun
    (extendDerivation_compAlgebraMap K K[X] K⟮X⟯ (nonZeroDivisors K[X])
      ((Algebra.linearMap K[X] K⟮X⟯).compDer
        (Polynomial.derivative' : Derivation K K[X] K[X]))) p
  exact h

/-- Finite-point Laurent expansion intertwines the rational derivative and
the formal Laurent derivative in the local parameter. -/
theorem atPoint_derivative (a : K) (f : K⟮X⟯) :
    atPoint K a (derivative K f) =
      LaurentSeries.derivative K (atPoint K a f) := by
  induction f using RatFunc.induction_on with
  | _ p q hq =>
      rw [Derivation.leibniz_div]
      simp only [smul_eq_mul, map_mul, map_sub, map_inv₀, map_pow,
        derivative_algebraMap, atPoint_algebraMap]
      rw [map_div₀]
      simp only [atPoint_algebraMap]
      change _ = LaurentSeries.spectralDerivation K
        (polynomialAtPoint K a p / polynomialAtPoint K a q)
      rw [Derivation.leibniz_div]
      simp only [LaurentSeries.spectralDerivation_apply,
        derivative_polynomialAtPoint, smul_eq_mul]

/-- Residue of a rational function at the finite point `a`. -/
def residueAtPoint (a : K) (f : K⟮X⟯) : K :=
  LaurentSeries.residue (atPoint K a f)

/-- The residue of a rational derivative vanishes at every finite point. -/
@[simp]
theorem residueAtPoint_derivative (a : K) (f : K⟮X⟯) :
    residueAtPoint K a (derivative K f) = 0 := by
  rw [residueAtPoint, atPoint_derivative]
  exact LaurentSeries.residue_derivative _

end RatFunc
