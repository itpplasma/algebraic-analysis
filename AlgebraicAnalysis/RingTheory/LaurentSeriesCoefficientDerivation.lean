/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.LaurentSeriesResidue

/-!
# Coefficientwise derivations of Laurent series

This module extends a derivation of the coefficient ring coefficientwise to
formal Laurent series.  The extension commutes with the spectral derivative
and with coefficient-extraction residue.

## Provenance

The interface is extracted from `itpplasma/jc2` at revision
`4a98d94ac3fbdbed7f4b4995c687e3870386e9bc`, originally from
`research/general-pq-carry-20260911/finite-moment-coordinates-all-m.md`,
equation (2).  Both repositories are Apache-2.0.  Authorship follows the
source repository history (Christopher Albert); this file supplies the Lean
implementation.  The declaration mapping is the note's assertion that
coefficient extraction commutes with the coefficient-field derivation to
`LaurentSeries.coefficientwiseDerivation_residue`, with
`LaurentSeries.derivative_coefficientwiseDerivation_commute` recording the
independent-variable commutation used by the downstream construction.
For expansions at infinity in the coordinate `X = s⁻¹`, the paper's
operators are exposed separately as `LaurentSeries.atInfinityDerivative`
(`d/ds = -X² d/dX`) and `LaurentSeries.residueAtInfinity` (`[X¹]`).
The current downstream consumer is `itpplasma/jc2-formal`, module
`JC2Formal/Corner/Moments.lean`.
-/

namespace AlgebraicAnalysis

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-- The formal Laurent derivative satisfies the Leibniz rule.  The proof uses
the Euler operator `X d/dX`, whose support is contained in the original
series support, and then recovers `d/dX` by multiplication by `X⁻¹`. -/
theorem LaurentSeries.derivative_mul {K : Type*} [CommRing K]
    (f g : LaurentSeries K) :
    LaurentSeries.derivative ℤ (f * g) =
      f * LaurentSeries.derivative ℤ g + g * LaurentSeries.derivative ℤ f := by
  classical
  let E (f : LaurentSeries K) : LaurentSeries K :=
    HahnSeries.single 1 1 * LaurentSeries.derivative ℤ f
  have hcoeff (f : LaurentSeries K) (n : ℤ) :
      (E f).coeff n = n • f.coeff n := by
    simp [E, HahnSeries.coeff_single_mul]
  have hsupport (f : LaurentSeries K) : (E f).support ⊆ f.support := by
    intro n hn
    change (E f).coeff n ≠ 0 at hn
    change f.coeff n ≠ 0
    intro hzero
    exact hn (by simp [hcoeff, hzero])
  have hmul (f g : LaurentSeries K) : E (f * g) = f * E g + E f * g := by
    ext n
    rw [hcoeff, HahnSeries.coeff_add,
      HahnSeries.coeff_mul_right' (x := f) (y := E g)
        (s := g.support) g.isPWO_support (hsupport g),
      HahnSeries.coeff_mul_left' (x := E f) (y := g)
        (s := f.support) f.isPWO_support (hsupport f)]
    rw [HahnSeries.coeff_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have hijsum : ij.1 + ij.2 = n := (Finset.mem_antidiagonal.mp hij).2.2
    rw [hcoeff, hcoeff, ← hijsum, add_smul]
    simp only [zsmul_eq_mul]
    ring
  have hrecover (f : LaurentSeries K) :
      LaurentSeries.derivative ℤ f = HahnSeries.single (-1) 1 * E f := by
    ext n
    simp [HahnSeries.coeff_single_mul, hcoeff, sub_neg_eq_add]
  rw [hrecover, hmul, hrecover f, hrecover g]
  ring

/-- The formal Laurent derivative, packaged as a derivation over any scalar
ring acting on the coefficient ring. -/
noncomputable def LaurentSeries.spectralDerivation
    (A : Type*) {K : Type*} [CommRing A] [CommRing K] [Algebra A K] :
    Derivation A (LaurentSeries K) (LaurentSeries K) := by
  let Ladd : LaurentSeries K →+ LaurentSeries K :=
    { toFun := fun f => LaurentSeries.derivative A f
      map_zero' := by exact map_zero (LaurentSeries.derivative A)
      map_add' := by intro f g; exact map_add (LaurentSeries.derivative A) f g }
  let L : @LinearMap A A _ _ (RingHom.id A)
      (LaurentSeries K) (LaurentSeries K) _ _
      Algebra.toModule HahnSeries.instModule :=
    @LinearMap.mk A A _ _ (RingHom.id A)
      (LaurentSeries K) (LaurentSeries K) _ _
      Algebra.toModule HahnSeries.instModule Ladd (by
        intro z f
        ext n
        simp [Ladd, Algebra.smul_def]
        have halg : algebraMap A (LaurentSeries K) z =
            HahnSeries.C (algebraMap A K z) := by
          rw [HahnSeries.algebraMap_apply']
          ext k
          cases k <;> simp [PowerSeries.algebraMap_apply]
        rw [halg, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
        simp
        ring)
  exact Derivation.mk' L (by
    intro f g
    change LaurentSeries.derivative A (f * g) =
      f * LaurentSeries.derivative A g + g * LaurentSeries.derivative A f
    exact LaurentSeries.derivative_mul f g)

@[simp]
theorem LaurentSeries.spectralDerivation_apply
    (A : Type*) {K : Type*} [CommRing A] [CommRing K] [Algebra A K]
    (f : LaurentSeries K) :
    LaurentSeries.spectralDerivation A f = LaurentSeries.derivative K f := rfl

/-- Extend a derivation of the coefficient ring coefficientwise to Laurent
series. -/
noncomputable def LaurentSeries.coefficientwiseDerivation
    (D : Derivation A R R) : Derivation A (LaurentSeries R) (LaurentSeries R) := by
  let Ladd : LaurentSeries R →+ LaurentSeries R :=
    { toFun := fun f => f.map D
      map_zero' := by ext n; simp
      map_add' := by intro f g; ext n; simp }
  let L : @LinearMap A A _ _ (RingHom.id A)
      (LaurentSeries R) (LaurentSeries R) _ _
      Algebra.toModule HahnSeries.instModule :=
    @LinearMap.mk A A _ _ (RingHom.id A)
      (LaurentSeries R) (LaurentSeries R) _ _
      Algebra.toModule HahnSeries.instModule Ladd (by
        intro z f
        ext n
        simp [Ladd, Algebra.smul_def]
        have halg : algebraMap A (LaurentSeries R) z =
            HahnSeries.C (algebraMap A R z) := by
          rw [HahnSeries.algebraMap_apply']
          ext k
          cases k <;> simp [PowerSeries.algebraMap_apply]
        rw [halg, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
        simp)
  exact Derivation.mk' L (by
    intro f g
    have hsupport (x : LaurentSeries R) : (x.map D).support ⊆ x.support := by
      intro n hn
      change D (x.coeff n) ≠ 0 at hn
      change x.coeff n ≠ 0
      intro hx
      apply hn
      rw [hx, D.map_zero]
    change (f * g).map D =
      f * g.map D + g * f.map D
    rw [mul_comm g (f.map D)]
    ext n
    rw [HahnSeries.map_coeff, HahnSeries.coeff_add]
    rw [HahnSeries.coeff_mul_right' (x := f) (y := g.map D)
      (s := g.support) g.isPWO_support (hsupport g),
      HahnSeries.coeff_mul_left' (x := f.map D) (y := g)
        (s := f.support) f.isPWO_support (hsupport f)]
    simp only [HahnSeries.map_coeff, HahnSeries.coeff_mul,
      map_sum, D.leibniz, Finset.sum_add_distrib, smul_eq_mul]
    apply congrArg₂ (.+.)
    · simp
    · simp [mul_comm])

@[simp]
theorem LaurentSeries.coefficientwiseDerivation_apply_coeff
    (D : Derivation A R R) (f : LaurentSeries R) (n : ℤ) :
    (LaurentSeries.coefficientwiseDerivation D f).coeff n = D (f.coeff n) := by
  simp [LaurentSeries.coefficientwiseDerivation]

/-- Coefficient differentiation and spectral differentiation commute. -/
theorem LaurentSeries.derivative_coefficientwiseDerivation_commute
    (D : Derivation A R R) (f : LaurentSeries R) :
    LaurentSeries.derivative R (LaurentSeries.coefficientwiseDerivation D f) =
      LaurentSeries.coefficientwiseDerivation D (LaurentSeries.derivative R f) := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    LaurentSeries.coefficientwiseDerivation_apply_coeff,
    LaurentSeries.coefficientwiseDerivation_apply_coeff,
    LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff]
  simp

/-- Coefficientwise differentiation commutes with Laurent coefficient
extraction at exponent `-1`. -/
theorem LaurentSeries.coefficientwiseDerivation_residue
    {R : Type*} [Field R] [Algebra A R]
    (D : Derivation A R R) (f : LaurentSeries R) :
    D (LaurentSeries.residue f) =
      LaurentSeries.residue (LaurentSeries.coefficientwiseDerivation D f) := by
  rw [LaurentSeries.residue_apply, LaurentSeries.residue_apply,
    LaurentSeries.coefficientwiseDerivation_apply_coeff]

/-- Differentiation with respect to `s` on a Laurent expansion in the
at-infinity coordinate `X = s⁻¹`, so `d/ds = -X² d/dX`. -/
noncomputable def LaurentSeries.atInfinityDerivative
    {K : Type*} [Field K] (f : LaurentSeries K) : LaurentSeries K :=
  -(HahnSeries.single 2 1 * LaurentSeries.derivative ℤ f)

@[simp]
theorem LaurentSeries.atInfinityDerivative_apply
    {K : Type*} [Field K] (f : LaurentSeries K) :
    LaurentSeries.atInfinityDerivative f =
      -(HahnSeries.single 2 1 * LaurentSeries.derivative ℤ f) := rfl

/-- The at-infinity derivative satisfies the Leibniz rule. -/
theorem LaurentSeries.atInfinityDerivative_mul
    {K : Type*} [Field K] (f g : LaurentSeries K) :
    LaurentSeries.atInfinityDerivative (f * g) =
      f * LaurentSeries.atInfinityDerivative g +
        g * LaurentSeries.atInfinityDerivative f := by
  simp only [LaurentSeries.atInfinityDerivative,
    LaurentSeries.derivative_mul]
  ring

/-- Paper residue in the coordinate `X = s⁻¹`: the coefficient of `X¹`. -/
noncomputable def LaurentSeries.residueAtInfinity
    {K : Type*} [Field K] : LaurentSeries K →ₗ[K] K :=
  HahnSeries.coeff.linearMap 1

@[simp]
theorem LaurentSeries.residueAtInfinity_apply
    {K : Type*} [Field K] (f : LaurentSeries K) :
    LaurentSeries.residueAtInfinity f = f.coeff 1 := rfl

/-- The residue at infinity of an at-infinity derivative vanishes. -/
@[simp]
theorem LaurentSeries.residueAtInfinity_atInfinityDerivative
    {K : Type*} [Field K] (f : LaurentSeries K) :
    LaurentSeries.residueAtInfinity
      (LaurentSeries.atInfinityDerivative f) = 0 := by
  rw [LaurentSeries.residueAtInfinity_apply,
    LaurentSeries.atInfinityDerivative_apply]
  simp [HahnSeries.coeff_single_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]

/-- The at-infinity derivative commutes with coefficientwise
differentiation. -/
theorem LaurentSeries.atInfinityDerivative_coefficientwiseDerivation_commute
    {K : Type*} [Field K] [Algebra A K]
    (D : Derivation A K K) (f : LaurentSeries K) :
    LaurentSeries.atInfinityDerivative
        (LaurentSeries.coefficientwiseDerivation D f) =
      LaurentSeries.coefficientwiseDerivation D
        (LaurentSeries.atInfinityDerivative f) := by
  rw [LaurentSeries.atInfinityDerivative_apply,
    LaurentSeries.atInfinityDerivative_apply]
  have hderivative :
      LaurentSeries.derivative ℤ
          (LaurentSeries.coefficientwiseDerivation D f) =
        LaurentSeries.coefficientwiseDerivation D
          (LaurentSeries.derivative ℤ f) := by
    ext n
    rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
      LaurentSeries.coefficientwiseDerivation_apply_coeff,
      LaurentSeries.coefficientwiseDerivation_apply_coeff,
      LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff]
    simp
  rw [hderivative, map_neg, Derivation.leibniz]
  simp only [smul_eq_mul]
  have hconst : LaurentSeries.coefficientwiseDerivation D
      (HahnSeries.single 2 (1 : K)) = 0 := by
    ext n
    rw [LaurentSeries.coefficientwiseDerivation_apply_coeff]
    by_cases hn : n = 2
    · subst n
      simp
    · rw [HahnSeries.coeff_single_of_ne hn]
      simp
  rw [hconst]
  simp

/-- Coefficientwise differentiation commutes with paper residue at infinity. -/
theorem LaurentSeries.coefficientwiseDerivation_residueAtInfinity
    {K : Type*} [Field K] [Algebra A K]
    (D : Derivation A K K) (f : LaurentSeries K) :
    D (LaurentSeries.residueAtInfinity f) =
      LaurentSeries.residueAtInfinity
        (LaurentSeries.coefficientwiseDerivation D f) := by
  rw [LaurentSeries.residueAtInfinity_apply,
    LaurentSeries.residueAtInfinity_apply,
    LaurentSeries.coefficientwiseDerivation_apply_coeff]

end AlgebraicAnalysis
