# AlgebraicAnalysis formal status

Updated 2026-09-15. This repository owns reusable, application-independent
Lean foundations; downstream Stafford, Björk, JC2, and Navier projects own
their application-specific proof assembly.

## Current boundary

- The Ore/PBW, localization, filtered-module, support, rank, and Hessian
  foundations in the public API are proved with ordinary Lean/Mathlib axioms
  only.
- `PowerSeries.subst_binomialSeries_div_pow` proves the arbitrary-tail
  fractional-binomial root identity used by downstream Laurent expansions;
  `PowerSeries.map_subst_binomialSeries` proves coefficient-ring naturality;
  its concrete coefficient oracle is in
  `AlgebraicAnalysisTest/BinomialSeriesRoot.lean`.
- `PowerSeries.reverseTrunc` packages fixed-degree exponent reversal after a
  power-series truncation, with an exact coefficient formula and degree bound;
  its concrete windowing oracle is in
  `AlgebraicAnalysisTest/PowerSeriesReverseTrunc.lean`.
- `Finset.sum_div_le_div_sum`, its `finsuppAntidiag` specialization, and the
  two residual-exponent inequalities control accumulated floor and truncated
  subtraction losses in finite filtered convolutions; concrete consumers are
  in `AlgebraicAnalysisTest/Combinatorics/FiniteFloorSum.lean`.
- `RatFunc.atInfinity` constructs the variable-inversion homomorphism into
  Laurent series, and `RatFunc.coeff_atInfinity_eq_polynomialPart` identifies
  its nonpositive Laurent coefficients with the Euclidean polynomial part;
  `RatFunc.order_atInfinity` identifies Laurent order with negative rational
  degree and supplies the support bound for filtered diagonal substitutions.
  The independent orientation and proper-fraction oracle is
  `AlgebraicAnalysisTest/RingTheory/RatFuncAtInfinity.lean`; the downstream
  consumer is `jc2-formal`'s cubic-chart expansion exchange.
- `AlgebraicAnalysis.BernsteinInequality` is statement-only and remains open;
  its field binder now explicitly requires `CharZero K`.
- The pre-repair arbitrary-field statement was false: the first Weyl algebra over
  `𝔽₂` acting on `𝔽₂[t]/(t²)` has a nonzero constant-filtered module of GK
  dimension zero, contradicting the displayed lower bound one. The exact
  independent check is
  `research/bernstein_characteristic_p_oracle.py`.

## Next valid work

Formalize the repaired characteristic-zero Bernstein theorem, including any
remaining nondegeneracy hypotheses required by the proof. Do not add an
application-specific axiom.
The boundary review is recorded in
`docs/review-bernstein-boundary.md`; the public README remains intentionally
short.
