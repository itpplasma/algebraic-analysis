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
The current downstream consumer is `itpplasma/jc2-formal`, module
`JC2Formal/Corner/Moments.lean`.
-/

namespace AlgebraicAnalysis

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

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

end AlgebraicAnalysis
