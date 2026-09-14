import AlgebraicAnalysis.RingTheory.PowerSeriesReverseTrunc

/-!
Independent behavioral check for fixed-degree power-series reversal.  The
coefficient beyond the requested window is deliberately nonzero and must be
discarded.
-/

noncomputable section

namespace PowerSeriesReverseTruncTest

open Polynomial PowerSeries

def sample : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 1 else if n = 1 then 2 else if n = 2 then 3 else
      if n = 3 then 4 else if n = 4 then 5 else 0

example : (reverseTrunc 3 sample).coeff 0 = 4 := by
  simp [sample]

example : (reverseTrunc 3 sample).coeff 1 = 3 := by
  simp [sample]

example : (reverseTrunc 3 sample).coeff 2 = 2 := by
  simp [sample]

example : (reverseTrunc 3 sample).coeff 3 = 1 := by
  simp [sample]

/-- The nonzero coefficient outside the requested window is discarded. -/
example : (reverseTrunc 3 sample).coeff 4 = 0 := by
  simp [sample]

example : (reverseTrunc 3 sample).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_reverseTrunc_le 3 sample
  · simp [sample, coeff_reverseTrunc]

end PowerSeriesReverseTruncTest
