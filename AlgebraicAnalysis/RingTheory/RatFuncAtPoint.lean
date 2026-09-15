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
this derivative. It computes the residue of an inverse square at a simple
polynomial root and proves that the residue at every finite point of a rational
derivative vanishes.

## Provenance

The finite-point residue argument is extracted from `itpplasma/jc2` at
revision `4a7add6104d021c2f2f3b0e903f66d15096b56c9`, file
`research/general-pq-carry-20260911/finite-moment-coordinates-all-m.md`,
section 3, graph node `direct-finite-moment-coordinates-all-m`. The source
repository's license is not asserted here. Authorship of the mathematical
argument follows that repository's history (Christopher Albert); this file
supplies the Lean implementation. `RatFunc.atPoint`, `RatFunc.derivative`,
`RatFunc.residueAtPoint_inverse_sq_algebraMap`, and
`RatFunc.residueAtPoint_derivative` implement respectively the note's local
Laurent expansion, rational derivative, simple-root inverse-square residue
formula, and zero-residue-of-a-derivative step.
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

private theorem coeff_one_inv {K : Type*} [Field K] (u : PowerSeries K) :
    PowerSeries.coeff 1 u⁻¹ =
      -(PowerSeries.constantCoeff u)⁻¹ * PowerSeries.coeff 1 u *
        (PowerSeries.constantCoeff u)⁻¹ := by
  rw [PowerSeries.coeff_inv]
  have hanti : Finset.HasAntidiagonal.antidiagonal (A := Nat) 1 =
      ({(0, 1), (1, 0)} : Finset (Nat × Nat)) := rfl
  rw [hanti]
  simp [PowerSeries.constantCoeff_inv]
  ring

private theorem residue_inverse_sq_X_mul {K : Type*} [Field K]
    (u : PowerSeries K) (hu : PowerSeries.constantCoeff u ≠ 0) :
    LaurentSeries.residue
        ((HahnSeries.ofPowerSeries ℤ K (PowerSeries.X * u))⁻¹ ^ 2) =
      PowerSeries.coeff 1 (u⁻¹ ^ 2) := by
  let F : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K
  have hFu : F u ≠ 0 := by
    intro h
    have huz : u = 0 :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa [F] using h)
    exact hu (by simp [huz])
  have hF_inv : (F u)⁻¹ = F u⁻¹ := by
    apply mul_left_cancel₀ hFu
    rw [mul_inv_cancel₀ hFu, ← map_mul, PowerSeries.mul_inv_cancel u hu, map_one]
  rw [map_mul, show F PowerSeries.X = HahnSeries.single 1 1 by simp [F],
    mul_inv_rev, HahnSeries.inv_single, inv_one, hF_inv]
  have heq :
      (F u⁻¹ * (HahnSeries.single (-1) 1 : LaurentSeries K)) ^ 2 =
        HahnSeries.single (-2) 1 * F (u⁻¹ ^ 2) := by
    rw [pow_two, map_pow]
    have hs :
        (HahnSeries.single (-1) 1 : LaurentSeries K) * HahnSeries.single (-1) 1 =
          HahnSeries.single (-2) 1 := by
      rw [HahnSeries.single_mul_single]
      norm_num
    rw [← hs]
    ring
  rw [heq, LaurentSeries.residue_apply, HahnSeries.coeff_single_mul]
  norm_num
  rw [← map_pow]
  exact HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (u⁻¹ ^ 2) 1

/-- At a simple root `a` of a polynomial `M`, the residue of `1 / M²` is
`-M''(a) / M'(a)³`. -/
theorem residueAtPoint_inverse_sq_algebraMap [CharZero K]
    (M : K[X]) (a : K) (hroot : M.eval a = 0)
    (hsimple : M.derivative.eval a ≠ 0) :
    residueAtPoint K a ((algebraMap K[X] K⟮X⟯ M)⁻¹ ^ 2) =
      -M.derivative.derivative.eval a / (M.derivative.eval a) ^ 3 := by
  let t : PowerSeries K := ((Polynomial.taylor a M : K[X]) : PowerSeries K)
  let u : PowerSeries K := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) t
  have ht0 : PowerSeries.constantCoeff t = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simpa [t, Polynomial.taylor_coeff_zero] using hroot
  have ht : t = PowerSeries.X * u := by
    rw [PowerSeries.eq_X_mul_shift_add_const t, ht0]
    simp [u]
  have hu0 : PowerSeries.constantCoeff u = M.derivative.eval a := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [u, t, Polynomial.taylor_coeff_one]
  have hu : PowerSeries.constantCoeff u ≠ 0 := hu0.symm ▸ hsimple
  have hcoeff :
      PowerSeries.coeff 1 (u⁻¹ ^ 2) =
        -2 * PowerSeries.coeff 1 u / (PowerSeries.constantCoeff u) ^ 3 := by
    rw [PowerSeries.coeff_one_pow]
    rw [show 2 - 1 = 1 by decide, pow_one]
    rw [PowerSeries.constantCoeff_inv, coeff_one_inv]
    simp only [Nat.cast_ofNat]
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  have hsecond :
      2 * (Polynomial.hasseDeriv 2 M).eval a =
        M.derivative.derivative.eval a := by
    have h := congrArg (fun p : K[X] => p.eval a)
      (congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) 2) M)
    simpa [Function.iterate_succ_apply, nsmul_eq_mul] using h
  calc
    residueAtPoint K a ((algebraMap K[X] K⟮X⟯ M)⁻¹ ^ 2) =
        LaurentSeries.residue
          ((HahnSeries.ofPowerSeries ℤ K t)⁻¹ ^ 2) := by
      simp [residueAtPoint, polynomialAtPoint_eq_taylor, t]
    _ = LaurentSeries.residue
          ((HahnSeries.ofPowerSeries ℤ K (PowerSeries.X * u))⁻¹ ^ 2) := by
      rw [← ht]
    _ = PowerSeries.coeff 1 (u⁻¹ ^ 2) := residue_inverse_sq_X_mul u hu
    _ = -2 * PowerSeries.coeff 1 u / (PowerSeries.constantCoeff u) ^ 3 := hcoeff
    _ = -M.derivative.derivative.eval a / (M.derivative.eval a) ^ 3 := by
      rw [hu0]
      have hu1 : PowerSeries.coeff 1 u = (Polynomial.hasseDeriv 2 M).eval a := by
        simp [u, t, Polynomial.taylor_coeff]
      rw [hu1, ← hsecond]
      ring

/-- The residue of a rational derivative vanishes at every finite point. -/
@[simp]
theorem residueAtPoint_derivative (a : K) (f : K⟮X⟯) :
    residueAtPoint K a (derivative K f) = 0 := by
  rw [residueAtPoint, atPoint_derivative]
  exact LaurentSeries.residue_derivative _

end RatFunc
