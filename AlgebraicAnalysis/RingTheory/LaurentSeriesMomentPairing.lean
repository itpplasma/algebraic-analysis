/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.LaurentSeriesCoefficientDerivation
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite Laurent moment pairings

A normalized family with leading terms `X¹, …, Xⁿ` pairs invertibly, by
residue at infinity, with the finite spectral window
`1, X⁻¹, …, X⁻⁽ⁿ⁻¹⁾`.  The pairing matrix is upper unit triangular.

## Provenance

The interface is extracted from `itpplasma/jc2` at revision
`4a7add6104d021c2f2f3b0e903f66d15096b56c9`, file
`research/general-pq-carry-20260911/finite-moment-coordinates-all-m.md`,
equation (3), graph node `direct-finite-moment-coordinates-all-m`. This Lean
implementation is Apache-2.0; the source repository's
license is not asserted here. Authorship follows the source repository history
(Christopher Albert); this file supplies the reusable Lean implementation.
The downstream consumer is `itpplasma/jc2-formal`, module
`JC2Formal/Corner/Moments.lean`.
-/

namespace AlgebraicAnalysis

noncomputable section

variable {K : Type*} [Field K]

/-- The Laurent representative of a polynomial in `s = X⁻¹` with coefficient
window indexed by `Fin N`. -/
def LaurentSeries.spectralPolynomialWindow {N : ℕ} (q : Fin N → K) :
    LaurentSeries K :=
  ∑ k : Fin N, HahnSeries.single (-(k : ℤ)) (q k)

/-- Residue-pairing matrix for a family whose row `j` is intended to start
with `X^(j+1)`. -/
def LaurentSeries.momentPairingMatrix {N : ℕ}
    (root : Fin N → LaurentSeries K) : Matrix (Fin N) (Fin N) K :=
  fun j k ↦ (root j).coeff (1 + (k : ℤ))

theorem LaurentSeries.residueAtInfinity_mul_spectralPolynomialWindow
    {N : ℕ} (root : Fin N → LaurentSeries K) (q : Fin N → K)
    (j : Fin N) :
    LaurentSeries.residueAtInfinity
        (root j * LaurentSeries.spectralPolynomialWindow q) =
      (LaurentSeries.momentPairingMatrix root).mulVec q j := by
  rw [LaurentSeries.residueAtInfinity_apply,
    LaurentSeries.spectralPolynomialWindow, Finset.mul_sum,
    HahnSeries.coeff_sum]
  simp [LaurentSeries.momentPairingMatrix, Matrix.mulVec, dotProduct,
    HahnSeries.coeff_mul_single, sub_neg_eq_add]

/-- Leading coefficient one and no lower exponents make the finite moment
pairing matrix injective. No coefficient of the input window is inverted. -/
theorem LaurentSeries.momentPairingMatrix_injective {N : ℕ}
    (root : Fin N → LaurentSeries K)
    (hlow : ∀ j : Fin N, ∀ z : ℤ, z < (j : ℤ) + 1 →
      (root j).coeff z = 0)
    (hdiag : ∀ j : Fin N, (root j).coeff ((j : ℤ) + 1) = 1) :
    Function.Injective (LaurentSeries.momentPairingMatrix root).mulVec := by
  have hupper :
      (LaurentSeries.momentPairingMatrix root).IsUpperTriangular := by
    intro i j hji
    apply hlow
    change j < i at hji
    have hcast : (j : ℤ) < (i : ℤ) := by exact_mod_cast hji
    omega
  have hdet : (LaurentSeries.momentPairingMatrix root).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hupper]
    apply Finset.prod_eq_one
    intro i hi
    simpa [LaurentSeries.momentPairingMatrix, add_comm] using hdiag i
  apply Matrix.mulVec_injective_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, hdet]
  exact isUnit_one

/-- The paper's finite residue pairing is injective on polynomial spectral
windows whenever the chosen negative fractional powers have their normalized
leading terms. -/
theorem LaurentSeries.residueAtInfinity_monicPairing_injective {N : ℕ}
    (root : Fin N → LaurentSeries K)
    (hlow : ∀ j : Fin N, ∀ z : ℤ, z < (j : ℤ) + 1 →
      (root j).coeff z = 0)
    (hdiag : ∀ j : Fin N, (root j).coeff ((j : ℤ) + 1) = 1) :
    Function.Injective (fun q : Fin N → K ↦ fun j : Fin N ↦
      LaurentSeries.residueAtInfinity
        (root j * LaurentSeries.spectralPolynomialWindow q)) := by
  intro q r hqr
  apply LaurentSeries.momentPairingMatrix_injective root hlow hdiag
  funext j
  rw [← LaurentSeries.residueAtInfinity_mul_spectralPolynomialWindow,
    ← LaurentSeries.residueAtInfinity_mul_spectralPolynomialWindow]
  exact congrFun hqr j

/-- Kernel form of `residueAtInfinity_monicPairing_injective`. -/
theorem LaurentSeries.spectralPolynomialWindow_eq_zero_of_pairings {N : ℕ}
    (root : Fin N → LaurentSeries K)
    (hlow : ∀ j : Fin N, ∀ z : ℤ, z < (j : ℤ) + 1 →
      (root j).coeff z = 0)
    (hdiag : ∀ j : Fin N, (root j).coeff ((j : ℤ) + 1) = 1)
    (q : Fin N → K)
    (hpair : ∀ j : Fin N, LaurentSeries.residueAtInfinity
      (root j * LaurentSeries.spectralPolynomialWindow q) = 0) :
    LaurentSeries.spectralPolynomialWindow q = 0 := by
  have hq : q = 0 :=
    (LaurentSeries.residueAtInfinity_monicPairing_injective root hlow hdiag)
      (by
        funext j
        change LaurentSeries.residueAtInfinity
          (root j * LaurentSeries.spectralPolynomialWindow q) =
            LaurentSeries.residueAtInfinity
              (root j * LaurentSeries.spectralPolynomialWindow
                (0 : Fin N → K))
        rw [hpair j]
        simp [LaurentSeries.spectralPolynomialWindow])
  simp [hq, LaurentSeries.spectralPolynomialWindow]

end

end AlgebraicAnalysis
