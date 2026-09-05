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
