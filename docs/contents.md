# Library contents

A short tour of `AlgebraicAnalysis/`. All results are stated with explicit
hypotheses (finiteness, Noetherian, localization and module assumptions are
kept as arguments rather than global instances). The library contains no
`sorry` and no `axiom` declarations. Sources for the mathematics are listed
in [literature.md](literature.md); the origin of declarations extracted from
downstream projects is in [provenance.yaml](provenance.yaml).

## Ore extensions (`Ore/`)

Ore extensions by a derivation, with explicit coefficient order: associativity,
left and right PBW bases, iterated towers, finite right PBW bases for monic
principal quotients, right division and normal forms, primitives for finite
right-Ore intersections and minimal-degree principal right ideals, Noetherian
properties, and right Ore localization. `Ore/ActiveCoordinate.lean`
(namespace `AlgebraicAnalysis.OreActiveCoordinate`) collects the coordinate
and coefficient relations of an Ore extension.

## Derivations and commutators (`Derivation/`, `Commutator.lean`, `CommutatorRiccati.lean`)

Central derivations, central-coordinate escape, Jacobian exactness, and
inverse-Euler/Riccati commutator identities.

## Differential operators (`DifferentialOperators/`)

Grothendieck's finite-order differential operators defined by iterated
commutators, generation by coordinate derivations, and differential operators
and derivations on localized polynomial rings. The order filtration of
`D_k(R)` (commutators drop the order, first-order operators are
multiplications plus derivations), the coordinate symbol presentation
`R[ξ] ↠ gr D_k(R)` with its Noetherian and deviation consequences, and
`D_k(k[x₁, …, xₙ]) ≅ A_n(k)` in characteristic zero (simple domain, infinite
centre). Projective frames (`Ω_{R/k}` projective) give `R[ξ] ↠ gr D_k(R)`
without coordinates; `D_k(R)` is a domain for every domain `R` and simple when
`R` has no differential ideals. For a smooth algebra `A` in characteristic
zero, `D_k(A)` is right and left Noetherian with deviation at most twice the
number of generators, and for a smooth domain it is simple with infinite
centre (`SmoothOperators`).

## Modules (`Module/`)

Filtered two-term complexes (pages, actions, naturality, boundary
exhaustion), a filtered Schreyer equivalence that turns a lower-order
right-ideal problem into a source relation (with the strictness hypothesis
explicit), localized kernel/cokernel length comparisons at minimal support
primes, Koszul-type positivity for principal ideals, denominator torsion,
unimodular splitting, and the determinant-trick support exclusion for a
finite module on which a chosen scalar acts surjectively.

## Filtrations (`Filtration/`)

Ascending ring filtrations with associated graded pieces and order function;
good filtrations on modules, their existence for finitely generated modules,
and the bounded-shift comparison of any two good filtrations; Hilbert
functions of filtrations by finite-dimensional subspaces, with growth degree
in the extended reals, invariant under bounded shifts; and Gelfand-Kirillov
dimension. Symbol presentations of the associated graded module by a
polynomial ring over the degree-zero part when the associated graded module is
commutative and generated in degree one. `gkDim_totalDegreeFiltration` shows that the polynomial ring in
`n` variables with its total-degree filtration has GK dimension `n`.

`GKDimension.BernsteinInequality` states the Bernstein inequality over
fields of characteristic zero as a `Prop`. It is not proved and is not used
as a hypothesis. The characteristic-zero assumption is needed: the script
`research/bernstein_characteristic_p_oracle.py` checks a Weyl-module
counterexample in characteristic two.

## Polynomial maps (`HessianAlgebra/`, `Polynomial/`)

The `HessianAlgebra` library (also built as the separate Lake target
`AlgebraicAnalysisHessian`): polynomial self-maps, formal differentiation,
affine and triangular inverses, coordinate changes, Hessians and homogeneous
support. `Polynomial/DistinguishedVariable.lean` proves a distinguished-axis
lemma for homogeneous relations in prime ideals.

## Other

- `FieldTheory/FunctionField.lean`: the fraction field of a finitely
  generated domain is finitely generated as an intermediate field
  (`top_fg_of_finiteType_fractionRing`).
- `RingTheory/`: Laurent and power series (residues, fractional powers,
  moment pairings), rational functions at a point and at infinity, and the
  two-generator identity `1 = d R + F d S` as a ring property, with transport
  along unit-clearing maps and Ore localization (`TwoGeneratorIdentity.lean`).
- `RingTheory/Goldie/` (namespace `AlgebraicAnalysis.Goldie`): Goldie theory
  for a simple right Noetherian ring `R`. `Basic.lean`: the singular ideal
  vanishes, essential right ideals contain regular elements, the right Ore
  condition, and every right ideal `I` contains `a` with `I/aR`
  Goldie-torsion. `Torsion.lean`: Goldie-torsion modules, common regular
  annihilators, escape with singular tails. `QuotientRing.lean`: Goldie's
  theorem, the classical right quotient ring is simple, semisimple and
  Artinian, hence a matrix ring over a division ring. `Rank.lean`: the module
  of fractions `M_Q`, the Goldie-torsion part `t(M)` as the kernel of
  `M → M_Q`, the Goldie rank `length_Q(M_Q)` (additive, `m · rk R` on `Rᵐ`,
  zero exactly on Goldie-torsion modules, finite for finitely generated `M`),
  and its equality with the uniform dimension of `M/t(M)` and of `R_R`.
  `Idempotents.lean`: complete orthogonal idempotents `Eᵢ` of `Q` with `EᵢQ`
  simple and common denominators in `R`. `Splitting.lean`: if
  `rk(R_R) ≤ rk(M)`, some `p ∈ M` has zero annihilator and
  `rk(M) = rk(R_R) + rk(M/pR)`; for nonzero `e_j` and `rk(M) < n`, elements
  `m_j e_j` whose fractions span `M_Q`. `RingTheory/SimpleArtinian.lean`: over
  a simple Artinian ring, `length A ≤ length X` gives an embedding `A ↪ X`.
- `Module/UniformDimension.lean`: uniform dimension as `iSupIndep` predicates
  `UniformDimGE`, `UniformDimLE`; it is bounded by length and equals length for
  semisimple modules. `Ore/ModuleLocalization.lean`: exactness of Ore
  localization of modules, its torsion kernel, and preservation of uniform
  dimension under essential embeddings into localized modules.
- `LinearAlgebra/`: division and activated pencils, finite Taylor
  reconstruction.
- `Order/`, `Combinatorics/`: deviation of posets and a finite floor-sum
  identity.

## Tests

`AlgebraicAnalysisTest/` exercises the public API; run it with `lake test`.
