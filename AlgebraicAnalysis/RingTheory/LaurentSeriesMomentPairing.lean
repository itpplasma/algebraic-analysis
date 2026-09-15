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
equations (3) and (5), graph node `direct-finite-moment-coordinates-all-m`. This Lean
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

/-- The first `N` positive Laurent coefficients, representing
`t₁X + ⋯ + t_N X^N`. -/
def LaurentSeries.positiveTailWindow {N : ℕ} (t : Fin N → K) :
    LaurentSeries K :=
  ∑ k : Fin N, HahnSeries.single ((k : ℤ) + 1) (t k)

/-- Residue pairing of a finite positive tail with a Laurent series. -/
theorem LaurentSeries.residueAtInfinity_positiveTailWindow_mul
    {N : ℕ} (t : Fin N → K) (H : LaurentSeries K) :
    LaurentSeries.residueAtInfinity
        (LaurentSeries.positiveTailWindow t * H) =
      ∑ k : Fin N, t k * H.coeff (-(k : ℤ)) := by
  rw [LaurentSeries.residueAtInfinity_apply,
    LaurentSeries.positiveTailWindow, Finset.sum_mul,
    HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [HahnSeries.coeff_single_mul]

/-- Split the last coefficient from a finite positive-tail residue pairing.
When `c = m`, its negation is the triangular `-m t_N` term in equation (5)
of the all-`m` moment calculation. -/
theorem LaurentSeries.residueAtInfinity_positiveTailWindow_mul_triangular
    (N : ℕ) (t : Fin (N + 1) → K) (H : LaurentSeries K) (c : K)
    (hlead : H.coeff (-(N : ℤ)) = c) :
    -LaurentSeries.residueAtInfinity
        (LaurentSeries.positiveTailWindow t * H) =
      -(c * t (Fin.last N)) -
        ∑ k ∈ (Finset.univ.erase (Fin.last N)),
          t k * H.coeff (-(k : ℤ)) := by
  rw [LaurentSeries.residueAtInfinity_positiveTailWindow_mul]
  have hmem : Fin.last N ∈ (Finset.univ : Finset (Fin (N + 1))) :=
    Finset.mem_univ _
  have hlast : H.coeff (-((Fin.last N : Fin (N + 1)) : ℤ)) = c := by
    simpa using hlead
  rw [← Finset.sum_erase_add Finset.univ
    (fun k : Fin (N + 1) => t k * H.coeff (-(k : ℤ))) hmem, hlast]
  ring

/-- The coefficient of a product at the sum of two exact leading exponents. -/
theorem LaurentSeries.coeff_mul_of_leadingTerms
    (f g : LaurentSeries K) (a b : ℤ) (A B : K)
    (hflow : ∀ z : ℤ, z < a → f.coeff z = 0)
    (hfa : f.coeff a = A) (hA : A ≠ 0)
    (hglow : ∀ z : ℤ, z < b → g.coeff z = 0)
    (hgb : g.coeff b = B) (hB : B ≠ 0) :
    (f * g).coeff (a + b) = A * B := by
  have hfcoeff : f.coeff a ≠ 0 := hfa.symm ▸ hA
  have hgcoeff : g.coeff b ≠ 0 := hgb.symm ▸ hB
  have hfne : f ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hfcoeff
  have hgne : g ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hgcoeff
  have hforderTop : f.orderTop = (a : WithTop ℤ) := by
    apply le_antisymm
    · exact HahnSeries.orderTop_le_of_coeff_ne_zero hfcoeff
    · rw [HahnSeries.le_orderTop_iff_forall]
      intro z hz
      apply hflow z
      exact_mod_cast hz
  have hgorderTop : g.orderTop = (b : WithTop ℤ) := by
    apply le_antisymm
    · exact HahnSeries.orderTop_le_of_coeff_ne_zero hgcoeff
    · rw [HahnSeries.le_orderTop_iff_forall]
      intro z hz
      apply hglow z
      exact_mod_cast hz
  have hforder : f.order = a := by
    apply WithTop.coe_eq_coe.mp
    exact (HahnSeries.order_eq_orderTop_of_ne_zero hfne).trans hforderTop
  have hgorder : g.order = b := by
    apply WithTop.coe_eq_coe.mp
    exact (HahnSeries.order_eq_orderTop_of_ne_zero hgne).trans hgorderTop
  rw [← hforder, ← hgorder, HahnSeries.coeff_mul_order_add_order,
    HahnSeries.leadingCoeff_of_ne_zero hfne,
    HahnSeries.leadingCoeff_of_ne_zero hgne]
  simpa [hforderTop, hgorderTop] using congrArg₂ (· * ·) hfa hgb

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
