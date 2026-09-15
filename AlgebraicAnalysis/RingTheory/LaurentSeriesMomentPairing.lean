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

@[simp]
theorem LaurentSeries.positiveTailWindow_coeff_at
    {N : ℕ} (t : Fin N → K) (k : Fin N) :
    (LaurentSeries.positiveTailWindow t).coeff ((k : ℤ) + 1) = t k := by
  rw [LaurentSeries.positiveTailWindow, HahnSeries.coeff_sum]
  calc
    (∑ i : Fin N,
        ((HahnSeries.single ((i : ℤ) + 1)) (t i)).coeff ((k : ℤ) + 1)) =
        ((HahnSeries.single ((k : ℤ) + 1)) (t k)).coeff ((k : ℤ) + 1) := by
      apply Finset.sum_eq_single k
      · intro b _hb hne
        rw [HahnSeries.coeff_single_of_ne]
        intro heq
        apply hne
        apply Fin.ext
        exact_mod_cast (add_right_cancel heq).symm
      · simp
    _ = t k := by simp

theorem LaurentSeries.positiveTailWindow_coeff_eq_zero_of_nonpos
    {N : ℕ} (t : Fin N → K) (z : ℤ) (hz : z ≤ 0) :
    (LaurentSeries.positiveTailWindow t).coeff z = 0 := by
  rw [LaurentSeries.positiveTailWindow, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro k _hk
  rw [HahnSeries.coeff_single_of_ne]
  omega

/-- The product of two Laurent series vanishes strictly below the sum of
their lower coefficient bounds. -/
theorem LaurentSeries.coeff_mul_eq_zero_of_lt_add
    (f g : LaurentSeries K) (a b z : ℤ)
    (hf : ∀ x : ℤ, x < a → f.coeff x = 0)
    (hg : ∀ y : ℤ, y < b → g.coeff y = 0)
    (hz : z < a + b) :
    (f * g).coeff z = 0 := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hsum : ij.1 + ij.2 = z := (Finset.mem_antidiagonal.mp hij).2.2
  by_cases hia : ij.1 < a
  · rw [hf _ hia, zero_mul]
  · have hia' : a ≤ ij.1 := le_of_not_gt hia
    have hib : ij.2 < b := by omega
    rw [hg _ hib, mul_zero]

/-- If `T` has only positive exponents and `H` starts at exponent `1-N`, then
the residue at infinity of `T * H` depends only on coefficients `1, …, N` of
`T`. -/
theorem LaurentSeries.residueAtInfinity_tail_eq_positiveTailWindow
    (T H : LaurentSeries K) (N : ℕ)
    (hT : ∀ z : ℤ, z ≤ 0 → T.coeff z = 0)
    (hH : ∀ z : ℤ, z < 1 - (N : ℤ) → H.coeff z = 0) :
    LaurentSeries.residueAtInfinity (T * H) =
      LaurentSeries.residueAtInfinity
        (LaurentSeries.positiveTailWindow
          (fun k : Fin N => T.coeff ((k : ℤ) + 1)) * H) := by
  let W := LaurentSeries.positiveTailWindow
    (fun k : Fin N => T.coeff ((k : ℤ) + 1))
  have hdiff : ∀ z : ℤ, z < (N : ℤ) + 1 → (T - W).coeff z = 0 := by
    intro z hz
    rw [HahnSeries.coeff_sub]
    by_cases hz0 : z ≤ 0
    · rw [hT _ hz0,
        LaurentSeries.positiveTailWindow_coeff_eq_zero_of_nonpos _ _ hz0,
        sub_zero]
    · have hklt : z.toNat - 1 < N := by omega
      let k : Fin N := ⟨z.toNat - 1, hklt⟩
      have hk : (k : ℤ) + 1 = z := by
        dsimp [k]
        omega
      rw [← hk, LaurentSeries.positiveTailWindow_coeff_at, sub_self]
  have hprod : ((T - W) * H).coeff 1 = 0 := by
    apply LaurentSeries.coeff_mul_eq_zero_of_lt_add
      (T - W) H ((N : ℤ) + 1) (1 - (N : ℤ)) 1 hdiff hH
    omega
  rw [sub_mul, HahnSeries.coeff_sub] at hprod
  rw [LaurentSeries.residueAtInfinity_apply,
    LaurentSeries.residueAtInfinity_apply]
  dsimp only [W] at hprod ⊢
  linear_combination hprod

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
