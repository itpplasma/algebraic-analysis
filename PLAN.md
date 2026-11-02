# AlgebraicAnalysis formal status

This repository owns reusable, application-independent
Lean foundations; downstream Stafford, Björk, JC2, and Navier projects own
their application-specific proof assembly.

The build uses Lean 4.35.0-rc3 and official Mathlib revision
`c55e6e786f49471c72fbddbec5415808896aec1e`. The full library, Hessian, and
test targets pass; independently imported core declarations use only the
standard Lean axioms. The toolchain migration changes exports and API usage
without changing the mathematical statements.

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
  used by expansions at infinity: `d/ds = -X² d/dX` and residue `[X¹]`; the
  coefficient formula and natural-power rule for the former are explicit.
  A mode `x^k (d/ds)(x^m) x⁻ʲ` has zero residue whenever `x ≠ 0` and `j < m`.
  Their
  concrete exponent/coefficient, hostile-orientation, and API oracles are in
  `AlgebraicAnalysisTest/RingTheory/LaurentSeriesCoefficientDerivation.lean`;
  the downstream consumer is `jc2-formal`'s finite-moment identity.
- `LaurentSeries.residueAtInfinity_monicPairing_injective` proves that the
  finite residue pairing between normalized leading terms `X¹,…,Xⁿ` and the
  polynomial spectral window `1,X⁻¹,…,X⁻⁽ⁿ⁻¹⁾` is injective, via its
  upper-unitriangular matrix. A concrete three-row oracle with arbitrary upper
  coefficients and a hostile missing-normalization control are in
  `AlgebraicAnalysisTest/RingTheory/LaurentSeriesMomentPairing.lean`; the
  same module also supplies the explicit positive-tail coefficient pairing,
  its last-coefficient triangular split, and the support cutoff showing that a
  residue only sees the required finite positive-tail window. The downstream
  consumers are equations (3) and (5) of `jc2-formal`'s finite-moment module.
- `LaurentSeries.monicNegativeFractionalPower` constructs the normalized
  expansion `X^j(1+u)^(-j/m)`, proves its lower coefficients vanish and its
  leading coefficient is one when `u` has zero constant term, and proves the
  exact relation `root^m * (X⁻ᵐ(1+u))^j = 1` when `m ≠ 0`. It also proves that
  `(dF/ds)F^(-j/m)` starts in exponent `1-m+j` with coefficient `m`, the
  diagonal input for equation (5), and that every `-j/m` row is the `j`th
  power of the `-1/m` row. Nontrivial cubic coefficient,
  Laurent-orientation, root-relation, and moment-factor oracles are in
  `AlgebraicAnalysisTest/RingTheory/LaurentSeriesFractionalPower.lean`; the
  downstream consumer instantiates the normalized roots in equation (3).
- `LaurentSeries.normalizedMomentFactorCoefficientPolynomial` and its
  evaluation theorem prove that every
  coefficient of `(dF/ds)F^(-j/m)` is a multivariate polynomial over `ℚ` in
  the positive coefficients of the zero-constant normalized monic tail. A
  nonzero two-coefficient cubic oracle checks specialization, two exact
  non-leading coefficients (including nonlinear dependence), and the leading
  exponent orientation. The definitions remain algebraically total at `m=0`,
  while their literal fractional-power interpretation requires `m≠0`. The
  downstream `jc2-formal` adapter renames these universal coefficient variables
  to its finite paper coefficients `D_i`.
- `RatFunc.atPoint` expands a rational function in the finite local parameter
  `s = X - a`; `RatFunc.derivative` extends ordinary polynomial
  differentiation through the fraction field, and `RatFunc.atPoint_derivative`
  proves that the expansion intertwines the two derivatives. Hence
  `RatFunc.residueAtPoint_derivative` gives zero residue for every rational
  derivative at every finite point, while
  `RatFunc.residueAtPoint_inverse_sq_algebraMap` computes
  `Res_a(1/M²) = -M''(a)/M'(a)³` at a simple root. Exact `1/X` residue,
  translated-coordinate, derivative hostile, and nonzero second-derivative
  checks are in
  `AlgebraicAnalysisTest/RingTheory/RatFuncAtPoint.lean`; the downstream
  consumer is the cubic finite-moment endpoint in `jc2-formal`.
- `AlgebraicAnalysis.BernsteinInequality` is statement-only and remains open;
  its field binder now explicitly requires `CharZero K`.
- The pre-repair arbitrary-field statement was false: the first Weyl algebra over
  `𝔽₂` acting on `𝔽₂[t]/(t²)` has a nonzero constant-filtered module of GK
  dimension zero, contradicting the displayed lower bound one. The exact
  independent check is
  `research/bernstein_characteristic_p_oracle.py`.

- `Order.DevLE`, `Module.DevLE` and `Module.Small` define finite
  Gabriel–Rentschler deviation on order intervals and submodule lattices
  (`DevLE 0` is Artinian; `Small 0` is subsingleton), with monotonicity,
  order-isomorphism and linear-equivalence invariance, submodule, quotient,
  extension and finite-product rules, and the principal-power chain bound in
  `Module/DeviationOmega.lean`; oracles in `AlgebraicAnalysisTest/Deviation.lean`
  (finite-dimensional spaces have deviation zero, `ℤ` has deviation one but
  not zero). Not `Order.krullDim` or commutative `supportDim`.
- `Module.devLE_of_ringKrullDim_le` (`Module/DeviationKrullDim.lean`) proves
  the upper bound of [MR 6.4.8]: a commutative Noetherian ring of Krull
  dimension at most `m` has ideal-lattice deviation at most `m`, via Mathlib's
  prime filtration and induction on prime coheight.
  `RingFiltration.GradedSymbol` (`Filtration/GradedSymbol.lean`) identifies
  the associated graded ring of a `RingFiltration` with a commutative graded
  algebra; `Filtration/SymbolNoetherian.lean` proves that `I ↦ gr I` is
  strictly monotone on right and on left ideals, hence [MR 1.6.9] (left and
  right Noetherian) and the two-sided deviation bounds `devLE_right`,
  `devLE_left`, `devLEOmega_right`, `devLEOmega_left`. Oracles in
  `AlgebraicAnalysisTest/Filtration/SymbolNoetherian.lean` (sharp bound for
  `ℤ` and `ℚ[X]`, symbol computations in `ℚ[X₀,X₁]`, agreement with Mathlib's
  Hilbert basis instance). The ring structure of `gr A` itself is not
  constructed; the hypothesis is the symbol identification.
  `Filtration/SymbolDomain.lean` proves that a symbol into a ring without zero
  divisors forces `A` to have none (`GradedSymbol.noZeroDivisors`, via the
  order function), and `GradedSymbol.isDomain` when `1 ∈ 𝒜 0`;
  `Weyl/Domain.lean` specializes the Bernstein symbol to
  `AlgebraicAnalysis.Weyl.noZeroDivisors` and the instance
  `AlgebraicAnalysis.Weyl.isDomain` for every field `k` (no characteristic
  hypothesis). Oracles in `AlgebraicAnalysisTest/Weyl.lean`.
- `RingFiltration.opposite` and `GradedSymbol.opposite` (`Filtration/Opposite.lean`)
  give the filtration and symbol of `Aᵐᵒᵖ` with the same commutative `G`.
  `rightIdealOpEquiv` and `leftIdealOpEquiv` identify ideal lattices of `Aᵐᵒᵖ`
  with those of `A`, so right-side Noetherianity and deviation of `Aᵐᵒᵖ` are the
  left-side statements for `A` (`isNoetherian_right_op_iff`, `devLE_right_op_iff`,
  and their companions). Oracle: `ℤᵐᵒᵖ` has right deviation exactly one.
- `RingFiltration.SymbolPresentation` (`Filtration/SymbolPresentation.lean`)
  replaces the isomorphism by a surjective multiplicative presentation `G ↠ gr A`,
  which need not be injective. The strict-monotonicity argument of
  `SymbolNoetherian` is unchanged, and `GradedSymbol.toPresentation` recovers the
  isomorphism case. Oracle: `ℚ[X₀,X₁]` presented by its own degree symbol
  (`AlgebraicAnalysisTest/Filtration/SymbolPresentation.lean`).
- PBW filtration of enveloping quotients (`Enveloping/PBWFiltration.lean`,
  `Enveloping/Presentation.lean`). For a Lie algebra `L` over a field and a surjective
  algebra map `π : U(L) → R`, the spans `Fₙ` of products of at most `n` Lie elements
  form a `RingFiltration`, and `pbwSymbolPresentation` is a surjective symbol
  presentation by `MvPolynomial (Fin m) k` with `m = dim L`. Consequences: `R` is
  Noetherian on both sides and `Module.DevLE` holds with bound `dim L` on both sides.
  Only the spanning direction of PBW is used (no injectivity claim). Oracle:
  `AlgebraicAnalysisTest/Enveloping/AbelianPBW.lean` (abelian `k^m`: the PBW
  filtration equals the total-degree filtration of `k[X]`).
  (`AlgebraicAnalysisTest/Filtration/SymbolPresentation.lean`). No filtration of an
  enveloping algebra is constructed yet.
- Differential operators `D_k(R)` (branch `diffops`, DX-1).
  `Filtration/PolynomialPresentation.lean`: a filtration with commutative
  associated graded module, `F 0 = ι(A)` and generated in degree one by
  `y₁, …, y_r` (`RingFiltration.PolynomialGenerators`) has the surjective
  presentation `A[X_σ] ↠ gr D`, hence Noetherian on both sides and deviation at
  most `dim A + r`. `DifferentialOperators/OrderFiltration.lean`, for every
  commutative `R`: `[D_m, D_n] ⊆ D_{m+n-1}` (`mul_sub_mul_mem_orderBelow`),
  `orderFiltration` with commutative associated graded module, and
  `D₁ ≅ R × Der_k(R)` (`orderOneEquiv`). `CoordinateSymbol.lean`: for algebra
  generators `xᵢ` with dual derivations, the Euler identity modulo lower order
  and (characteristic zero) filtered generation, so `D_k(R)` is generated by `R`
  and the `∂ᵢ` and is presented by `R[ξ]`. `PolynomialOperators.lean`:
  `D_k(k[x₁..xₙ])` in characteristic zero is right and left Noetherian with
  deviation at most `2n`, isomorphic to `A_n(k)` (`weylEquiv`), simple, a
  domain, with infinite centre. Oracles in
  `AlgebraicAnalysisTest/DifferentialOperatorsPolynomial.lean`.
- Coordinate frames and localized polynomial rings (branch `diffops-local`, DX-2).
  `CoordinateSymbol.lean` now works with `IsCoordinateFrame x D`: coordinates
  generating `R` up to unit denominators plus dual derivations, so localizations
  are covered. `Filtration/PolynomialSymbol.lean`: a polynomial presentation with
  dual coordinates (`[yᵢ, ι xⱼ] = δᵢⱼ`, `ι` injective) is injective in
  characteristic zero, hence `gr D ≅ A[ξ]` (`PolynomialGenerators.gradedSymbol`) and
  `D` is a domain when `A` is; applied as `IsCoordinateFrame.gradedSymbol`,
  `IsCoordinateFrame.isDomain`. `CoordinateSimplicity.lean`: `D_k(R)` is simple if
  `R` has no nonzero proper ideal stable under the derivations.
  `LocalizedPolynomialOperators.lean`: for `B = S⁻¹k[x₁..xₙ]` (char 0) `D_k(B)` is
  right and left Noetherian with deviation at most `2n` on both sides; for
  `S ≤ nonZeroDivisors` it is simple, a domain, with infinite centre
  (`ringKrullDim_le_of_isLocalization` gives `dim B ≤ n`). Oracles (Laurent
  polynomials, `ℚ(x₀, x₁)`, sharpness of the symbol) in
  `AlgebraicAnalysisTest/DifferentialOperatorsLocalized.lean`. D3 groundwork:
  `Localization.lean` (finite-order operators on `S⁻¹A` are determined on `A`,
  `eq_of_forall_algebraMap_eq`) and `SmoothDerivations.lean` (`Der_k A` finitely
  generated projective for smooth `A`); oracles in
  `AlgebraicAnalysisTest/DifferentialOperatorsD3.lean`.
- Smooth algebras (branch `diffops-smooth`, DX-3, stage D3 closed). For a field
  `k` of characteristic zero and a smooth `k`-algebra `A`,
  `SmoothOperators.lean` proves `D_k(A)` right and left Noetherian with
  deviation at most `2r` on both sides when `A` is generated by `r` elements
  (`devLE_right`, `devLE_left`, `devLEOmega_*`); for `A` a domain also simple,
  a domain, with infinite centre. Routes, chosen to avoid operator localization:
  `ProjectiveFrame.lean` (generators `xᵢ` and derivations `Eᵢ` with
  `d b = ∑ Eᵢ(b) d xᵢ`, existing iff `Ω` is projective; Euler identity, so
  `A[ξ] ↠ gr D`); `Domain.lean` (`D_k(R)` is a domain for every domain `R`,
  polarization of the principal symbol); `SmoothSimplicity.lean` (smooth domains
  have no differential ideals, via standard smooth opens, `A_g` unramified hence
  quasi-finite over `k[s₁..s_d]`, incomparability of fibre primes; then the
  frame-free criterion `isSimpleRing_of_derivation` in `CoordinateSimplicity.lean`,
  which replaces the coordinate-frame version). Oracles in
  `AlgebraicAnalysisTest/DifferentialOperatorsSmooth.lean`. Not needed and still
  open: existence of extensions of order-`n` operators to `S⁻¹A`, and
  `gr D_k(A) ≅ Sym_A(Der_k A)` (only the surjection is proved).
- `AlgebraicAnalysis.infinite_subring_center` (`RingTheory/InfiniteCenter.lean`):
  a nontrivial algebra over an infinite field has infinite centre (hypothesis `(Z)`).
- `Module.Critical` proves critical submodule existence and uniformity;
  `Module.CriticalFiltration` constructs finite critical filtrations for
  Noetherian finite-deviation modules and bounds non-small chain factors.
  `Module.LocSmall` supplies the locally small class, the shared small radical
  and density calculus; `Module.Germ` supplies additive germs and composition.
  The germ pair correspondence requires both Noetherian source and target.
  Concrete oracles are in `AlgebraicAnalysisTest/Critical.lean` and
  `AlgebraicAnalysisTest/Germ.lean`.
- `Ore/Noetherian.lean` proves the right Ore condition for right Noetherian
  domains and its equivalence with Mathlib's opposite-ring `OreSet`;
  `Module/ColonSupport.lean` proves the mixed-anchor colon maps and the bound
  for any class closed under submodules, quotients and extensions, plus the
  central-parameter inclusions; oracles in `AlgebraicAnalysisTest/OreColon.lean`.
- `LinearAlgebra/DivisionPencil.lean` extracts `central_eigenvectors_linearIndependent`,
  `pencil_ker_finite` and `division_pencil_finite` from generalized-stafford-formal
  46d9c6f (`GeneralizedStafford/DivisionPencil.lean`, Apache-2.0), with the
  downstream copy still to be removed in that repository's integration wave;
  `LinearAlgebra/ActivatedPencil.lean` proves the activated pencil
  (`T ∘ P = 0`, jointly injective `(P, T ∘ Q)` give finitely many bad central
  parameters) with no characteristic or infinite-field hypothesis; the reversed
  composition order is refuted in `AlgebraicAnalysisTest/DivisionPencil.lean`.
  Downstream consumer: the intrinsic Stafford formalization in
  generalized-stafford-formal.

- `Module.GermSchur`: for an e-critical Noetherian module C the germ
  endomorphisms form a division ring and germs R -> C form a uniform section
  module with commuting actions, torsion when C is. `Module.DualSeparation`
  proves the separation criterion and Hom dimension at most one for a
  critical target and existence of critical quotients.
  `Module.DualSeparationGeneral` proves left exactness of germ Hom along a
  submodule, finite Schur dimension bounded by the critical top length, the
  finite list of critical types, and separation for arbitrary germ sources
  over a Noetherian module of finite deviation; oracle in
  `AlgebraicAnalysisTest/DualSeparationGeneral.lean`. `Module.TorsionEscape` proves the torsion-bimodule
  escape lemma over a simple right Ore domain, the rank lemma and finite
  affine source selection. Oracles in `AlgebraicAnalysisTest/GermSchur.lean`
  and `TorsionEscape.lean`.

- `RingTheory/Goldie/` (namespace `AlgebraicAnalysis.Goldie`) is the
  authoritative home of Goldie theory for simple right Noetherian rings,
  extracted from generalized-stafford-formal 7697e11 and extended. `Basic`:
  vanishing singular ideal, essential right ideals contain regular elements,
  right Ore condition, and `exists_mem_forall_exists_mul_mem` (every right
  ideal `I` contains `a` with `I/aR` Goldie-torsion). `Torsion`:
  `IsGoldieTorsion`, closure, common regular annihilators, escape with
  singular tails, section modules. `QuotientRing`: Goldie's theorem, the
  classical right quotient ring `RightOreLocalization R R⁰` is simple,
  semisimple and Artinian, hence `Mₙ(D)` (Wedderburn–Artin), with finite
  positive length over itself. `Rank` (with `Ore/ModuleLocalization` and
  `Module/UniformDimension`): exact Ore localization of modules, Goldie rank
  `length_Q(M_Q)` and its equality with the uniform dimension of `M/t(M)` and
  of `R_R`. `Idempotents`: complete orthogonal idempotents of `Q` with common
  denominators in `R` (C.3 upper-bound device). Oracle in
  `AlgebraicAnalysisTest/RingTheory/GoldieRank.lean`. Oracle in `AlgebraicAnalysisTest/RingTheory/Goldie.lean`
  (`M₂(ℚ)` hostile control, `ℚ` with Mathlib's commutative Ore structure).
  Downstream generalized-stafford-formal must import these declarations and
  delete its copies; the Goldie affine source selection stays downstream.

## Next valid work

Formalize the repaired characteristic-zero Bernstein theorem, including any
remaining nondegeneracy hypotheses required by the proof. Do not add an
application-specific axiom.
The boundary review is recorded in
`docs/review-bernstein-boundary.md`; the public README remains intentionally
short.
