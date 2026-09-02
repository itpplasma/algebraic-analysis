# Extraction review: unimodular splitting and projective-image layer

## Boundary

This wave extracts the unconditional module-theoretic portion of Björk's
Stafford §3 work. The declarations quantify over rings, left modules, linear
functionals, finite module sequences, and explicit product equivalences. They
do not construct the required functionals from rank, assert two-simplicity,
use Ore localization, or prove any Stafford/Björk headline theorem.

| Source | Target | Scope |
| --- | --- | --- |
| `Bjork/Unimodular.lean` | `AlgebraicAnalysis/Module/Unimodular.lean` | unimodular elements, kernel projections, splitting equivalences, free cyclic summands, and projective kernels |
| `Bjork/FreeSummandInduction.lean` | `AlgebraicAnalysis/Module/FreeSummandInduction.lean` | finite iteration of normalized functional splittings |
| `Bjork/TorsionProjectiveImage.lean` | `AlgebraicAnalysis/Module/TorsionProjectiveImage.lean` | factorization and surjectivity through the first factor of a product; projective left-ideal image |

The original Björk paths remain import-only compatibility surfaces. The
right-module mirror and the two-functional construction remain downstream
because they depend on opposite-ring and two-simplicity interfaces specific
to the application.

## Provenance

- Source repository: `plasma/proj/bjork`
- Source revision: `2b398f0d8969b552133f33885bceab1988dabdc7`
- License: Apache-2.0, inherited from the source repository
- Authorship: inherited repository contribution; source history remains in
  Björk
- Current application consumer: Björk

## Evidence and limits

- The three target modules build with the ordinary Lean foundation.
- The package API test checks a concrete unimodular element, the
  surjectivity equivalence, and a product-factor surjection over `ℤ`.
- Björk's compatibility surfaces and full trust-zero axiom audit are the
  downstream integration checks after the package revision is pinned.
- The package does not assert that a suitable unimodular element exists in a
  given Stafford presentation, nor that a finite sequence of such elements
  can be produced. Those are downstream open inputs.
