import AlgebraicAnalysis.RingTheory.BinomialSeriesRoot

/-!
Independent API and coefficient checks for substituted fractional binomial
roots.  The concrete tail is `u = X²` and the exponent is `2/3`.
-/

noncomputable section

open PowerSeries

namespace BinomialSeriesRootTest

def tail : ℚ⟦X⟧ := X ^ 2

def root : ℚ⟦X⟧ := subst tail (binomialSeries ℚ (2 / 3 : ℚ))

example : constantCoeff tail = 0 := by simp [tail]

example : root ^ 3 = (1 + tail) ^ 2 := by
  exact subst_binomialSeries_div_pow tail (by simp [tail]) 2 3 (by decide)

/-- Independent low-order oracle: the first nonconstant coefficient follows
directly from the substitution coefficient formula, without the root identity. -/
example : coeff 2 root = 2 / 3 := by
  simp [root, tail, coeff_subst_X_pow]

end BinomialSeriesRootTest
