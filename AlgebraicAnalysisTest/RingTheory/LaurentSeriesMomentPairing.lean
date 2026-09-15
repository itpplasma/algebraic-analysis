/- SPDX-License-Identifier: Apache-2.0 -/

import AlgebraicAnalysis.RingTheory.LaurentSeriesMomentPairing
import Mathlib.Tactic

/-! Concrete unit-triangular and missing-normalization controls. -/

namespace AlgebraicAnalysis.LaurentSeries

noncomputable section

private def sampleRoot (j : Fin 3) : LaurentSeries ℚ :=
  HahnSeries.single ((j : ℤ) + 1) 1 +
    HahnSeries.single ((j : ℤ) + 2) 7

private theorem sampleRoot_low (j : Fin 3) (z : ℤ)
    (hz : z < (j : ℤ) + 1) : (sampleRoot j).coeff z = 0 := by
  rw [sampleRoot, HahnSeries.coeff_add,
    HahnSeries.coeff_single_of_ne (by omega),
    HahnSeries.coeff_single_of_ne (by omega)]
  simp

private theorem sampleRoot_diag (j : Fin 3) :
    (sampleRoot j).coeff ((j : ℤ) + 1) = 1 := by
  simp [sampleRoot]

/-- The test family has genuine, visible superdiagonal entries. -/
example :
    momentPairingMatrix sampleRoot 0 1 = 7 ∧
      momentPairingMatrix sampleRoot 1 2 = 7 ∧
        momentPairingMatrix sampleRoot 0 2 = 0 := by
  norm_num [momentPairingMatrix, sampleRoot]

/-- Upper coefficients may be arbitrary: the normalized leading terms still
give an injective three-row residue pairing. -/
example (q r : Fin 3 → ℚ)
    (h : ∀ j : Fin 3,
      residueAtInfinity (sampleRoot j * spectralPolynomialWindow q) =
        residueAtInfinity (sampleRoot j * spectralPolynomialWindow r)) :
    q = r := by
  exact residueAtInfinity_monicPairing_injective sampleRoot
    sampleRoot_low sampleRoot_diag (funext h)

/-- Hostile control: derivative compatibility alone cannot replace the
leading normalization, since the zero family annihilates every window. -/
example :
    (∀ _j : Fin 2, residueAtInfinity
      ((0 : LaurentSeries ℚ) * spectralPolynomialWindow ![1, 0]) = 0) ∧
      (![1, 0] : Fin 2 → ℚ) ≠ 0 := by
  constructor
  · intro j
    simp
  · intro h
    have := congrFun h 0
    norm_num at this

#print axioms AlgebraicAnalysis.LaurentSeries.momentPairingMatrix_injective
#print axioms AlgebraicAnalysis.LaurentSeries.residueAtInfinity_monicPairing_injective
#print axioms AlgebraicAnalysis.LaurentSeries.spectralPolynomialWindow_eq_zero_of_pairings

end

end AlgebraicAnalysis.LaurentSeries
