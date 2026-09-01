# Extraction review: one-stage PBW and commuting Ore towers

## Scope

This review covers the following existing Björk modules at source revision
`414131f`:

- `Bjork/OrePBW.lean`;
- `Bjork/RightOrePBW.lean`;
- `Bjork/OreTower.lean`;
- `Bjork/IteratedOreTower.lean`;
- `Bjork/IteratedPBW.lean`.

The proposed package homes are, respectively,
`AlgebraicAnalysis/Ore/LeftPBW.lean`, `RightPBW.lean`, `Tower.lean`,
`IteratedTower.lean`, and `IteratedPBW.lean`.

## Boundary decision

All five modules are application-independent. Their quantified data are rings,
fields, derivations, commuting hypotheses, finite lists, and polynomial/module
structures. They mention neither Stafford’s canonical quotient nor Björk’s
geometric or ideal-theoretic claims. The package will use neutral namespaces
under `AlgebraicAnalysis`; Björk will retain import-only compatibility through
its ordinary module graph while the declarations have one authoritative home.

The slice is intentionally limited to:

1. left and right PBW bases for one derivation-Ore stage;
2. coefficientwise lifting of a commuting derivation;
3. finite iterated towers and their additive normal-form equivalence;
4. the corresponding field-linear PBW basis.

Tower coefficient-extension, localization, rank, denominator, and
two-generation statements remain downstream until their APIs have an
independent second-consumer review.

## Evidence required before promotion

- the package modules compile under the pinned Lean/Mathlib toolchain;
- package tests exercise both left and right PBW APIs and a nontrivial
  commuting tower;
- Björk builds against the pinned package revision after its duplicate source
  modules are removed;
- Stafford38 has at least one concrete right-PBW consumer for its pair stage;
- source and consumer declarations pass `--trust=0` axiom audits;
- provenance records source revision, paths, namespaces, and consumers.

This is an extraction and API result only. It does not imply any result about
Stafford 3.8 or Björk’s two-generator conjecture.
