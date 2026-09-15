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
  degree. `RatFunc.orderTop_atInfinity_sub_polynomialPart_pos` proves that
  removing the polynomial part leaves only strictly positive Laurent degrees,
  while `RatFunc.neg_natDegree_polynomialPart_le_orderTop_atInfinity` bounds
  the full expansion below by the polynomial-part degree. Together these
  supply the truncation bounds for filtered diagonal substitutions and finite
  products.
  The independent orientation and proper-fraction oracle is
  `AlgebraicAnalysisTest/RingTheory/RatFuncAtInfinity.lean`; the downstream
  consumer is `jc2-formal`'s cubic-chart expansion exchange.
- `LaurentPolynomial.diagonalMap` gives the finite-support exponent regrading
  `(ell, q) ↦ (ell - q, q)`; `affineDiagonal_monomial` includes arbitrary
  affine shifts and fixes both exponent orientations. `affineDiagonal_pow`
  proves that taking a natural power scales both affine shifts, the exact law
  needed by downstream finite expansion exchange. Its concrete hostile
  orientation and power oracle is
  `AlgebraicAnalysisTest/RingTheory/LaurentDiagonal.lean`.
- `PowerSeries.LaurentAffineLower` packages affine lower-support bounds for
  power series with Laurent-series coefficients. Its same-slope and
  mixed-slope product laws yield the inclusive finite-power truncation bound
  in `LaurentAffineLower.pow_sub_coeff_zero_of_ge`; a threshold example and a
  hostile below-threshold mixed term are checked in
  `AlgebraicAnalysisTest/RingTheory/PowerSeriesLaurentSupport.lean`. The
  downstream consumer is `jc2-formal`'s radial/infinity expansion exchange.
- `PowerSeries.coeff_pow_eq_of_coeff_eq_of_le` shows that equality of a finite
  coefficient prefix is preserved at the corresponding coefficient by every
  natural-number power. `PowerSeries.coeff_eq_of_pow_coeff_eq_of_le` gives the
  converse finite triangular uniqueness for normalized power-series roots:
  equality of `n`-th-power coefficients through `K` recovers the root
  coefficients through `K` when the shared constant coefficient and `n` are
  nonzero in characteristic zero. Concrete forward and recovery examples and
  hostile controls are in
  `AlgebraicAnalysisTest/RingTheory/PowerSeriesPrefixRoot.lean`; the downstream
  consumer is `jc2-formal`'s finite radial/infinity expansion exchange.
- `LaurentSeries.spectralDerivation` packages the formal Laurent derivative
  with its Leibniz rule, while `LaurentSeries.coefficientwiseDerivation`
  extends a coefficient-ring derivation to Laurent series, commutes with the
  spectral derivative, and commutes with coefficient-extraction residue.
  `LaurentSeries.atInfinityDerivative` and
  `LaurentSeries.residueAtInfinity` expose the separate `X = s⁻¹` convention
  used by expansions at infinity: `d/ds = -X² d/dX` and residue `[X¹]`. Their
  concrete exponent/coefficient, hostile-orientation, and API oracles are in
  `AlgebraicAnalysisTest/RingTheory/LaurentSeriesCoefficientDerivation.lean`;
  the downstream consumer is `jc2-formal`'s finite-moment identity.
- `LaurentSeries.residueAtInfinity_monicPairing_injective` proves that the
  finite residue pairing between normalized leading terms `X¹,…,Xⁿ` and the
  polynomial spectral window `1,X⁻¹,…,X⁻⁽ⁿ⁻¹⁾` is injective, via its
  upper-unitriangular matrix. A concrete three-row oracle with arbitrary upper
  coefficients and a hostile missing-normalization control are in
  `AlgebraicAnalysisTest/RingTheory/LaurentSeriesMomentPairing.lean`; the
  downstream consumer is equation (3) of `jc2-formal`'s finite-moment module.
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
