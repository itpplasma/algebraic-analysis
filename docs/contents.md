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
and derivations on localized polynomial rings.

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
dimension. `gkDim_totalDegreeFiltration` shows that the polynomial ring in
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
- `LinearAlgebra/`: division and activated pencils, finite Taylor
  reconstruction.
- `Order/`, `Combinatorics/`: deviation of posets and a finite floor-sum
  identity.

## Tests

`AlgebraicAnalysisTest/` exercises the public API; run it with `lake test`.
