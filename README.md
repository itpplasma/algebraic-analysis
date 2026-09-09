# AlgebraicAnalysis

Reusable Lean foundations for Ore and Weyl algebras, filtered rings and
modules, algebraic differential operators, characteristic geometry, and
related exact certificates.

The repository contains reviewed Ore/PBW/tower foundations, including finite
right-PBW bases for monic principal Ore quotients and generic right-ideal
primitives for finite right-Ore intersections and minimal-degree principal
right ideals. It also contains application-independent Ore-localization,
localized-rank, split-rank, denominator-torsion, finite-filtration,
unimodular-splitting, projective-image, and inverse-Euler/Riccati commutator
primitives. Dependency pins and provenance are recorded in
`docs/provenance.yaml`.

The module layer also contains the determinant-trick support exclusion for a
finite module on which a chosen scalar acts surjectively.

The polynomial layer contains a scheme-theoretic distinguished-axis lemma for
homogeneous relations in prime ideals. It is a generic commutative-algebra
result with all hypotheses explicit.

The field-theory layer proves that the fraction field of a finitely generated
domain is finitely generated as an intermediate field, providing a precise
finite-generation statement for fraction fields.

The package contains generic central-coordinate escape, finite-tuple span, and
right-coordinate module primitives.

The active-coordinate Ore interface is available under
`AlgebraicAnalysis.OreActiveCoordinate`. It contains definitions and proofs
for the coordinate and coefficient relations of an Ore extension.

The package also defines neutral target interfaces for stable freeness and
localization of derivation-Ore extensions. These interfaces contain no axiom;
their hypotheses remain explicit at each use.

The package also exposes a ring/module-only filtered Schreyer equivalence for
translating a lower-order right-ideal problem into a source relation. Its
strictness hypothesis remains explicit.

The package also exposes generic filtered two-term page and action lemmas,
localization comparisons, support and finite-length arguments, and associated
polynomial-action primitives. These statements keep finiteness, Noetherian,
localization, and module hypotheses explicit.

All theorems in the public API have axiom-clean Lean proofs.

The package also contains a filtered-ring layer: ascending ring filtrations
with their associated graded pieces and order function; good filtrations on
modules, including existence for finitely generated modules and the comparison
lemma that any two good filtrations squeeze each other after a bounded shift;
Hilbert functions of filtrations by finite-dimensional subspaces, with growth
degree valued in the extended reals and proved invariant under bounded shifts;
and Gelfand-Kirillov dimension defined from that growth degree. The polynomial
ring in `n` variables with its total-degree filtration is proved to have
Gelfand-Kirillov dimension exactly `n`. The Bernstein inequality is stated as a
named proposition and is deliberately not proved; it is the open target of this
layer.

Current documentation release: **v0.3.1**. Adds the literature/source index and
module references; mathematical declarations and dependency pins are unchanged.

## Literature and source index

**[Literature → proof ingredients → Lean modules](docs/literature.md)** is the
starting point for tracing the mathematical foundations. It gives full
citations, source roles, module links, and the distinction between proved
imports, project constructions, background, and prior art.

**[Ore33]** Øystein Ore, *[Theory of Non-Commutative Polynomials](https://doi.org/10.2307/1968173)*, Annals of Mathematics (2) 34 (1933), no. 3, 480–508. Historical foundation for skew polynomial rings. The library implements the derivation case with explicit coefficient order, rather than all skew-polynomial generality.

**[StacksD]** The Stacks Project Authors, *[Finite order differential operators](https://stacks.math.columbia.edu/tag/09CH)*, The Stacks Project, Section 10.133, tag 09CH (accessed 2026-09-09). Background for the recursive commutator definition and localization of finite-order differential operators; Lean implementations and hypotheses are indexed below.

**[HTT08]** Ryoshi Hotta, Kiyoshi Takeuchi, and Toshiyuki Tanisaki, *[D-Modules, Perverse Sheaves, and Representation Theory](https://doi.org/10.1007/978-0-8176-4523-6)*, Progress in Mathematics 236, Birkhäuser, 2008. Background for differential operators, good filtrations and characteristic varieties (Chapters 1–2). No claim of a line-by-line formalization of this book.


## Build

```sh
lake exe cache get
lake build
lake test
lake lint
```

On macOS hosts where a cached `runLinter` executable predates the host dyld
format, run the same linter from Lean source:

```sh
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean AlgebraicAnalysis
```

## Release provenance

The [release history](docs/release-history.md) records exact downstream pins.
The [Zenodo metadata](.zenodo.json) describes v0.3.0.
