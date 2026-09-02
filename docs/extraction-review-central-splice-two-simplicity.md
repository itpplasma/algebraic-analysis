# Extraction review: central derivation and module primitives

Status: integrated.  The package API is authoritative at commit
`a0676c9e800b7c4783e8cf36e705ca82d6a719a1`; Björk consumes that immutable
revision through import-only compatibility surfaces.

## Scope

The slice moves three foundation-only groups from Björk:

- noncommutative additive derivation and centrality facts;
- simple-layer and maximal-submodule splice lemmas;
- the abstract transfer from principal-right-quotient torsion to
  two-simplicity.

The target modules import Mathlib only.  They contain no Weyl presentation,
localization construction, characteristic-variety argument, literature axiom,
or final Björk/Stafford theorem.

## Boundary audit

The centrality theorem takes a ring homomorphism, a source central element,
right-fraction representatives, and denominator units as hypotheses.  The
two-simplicity theorem takes the principal-right-quotient torsion property as
an explicit hypothesis.  These are interfaces for downstream constructions,
not claims that those hypotheses hold in a differential-operator ring.

All products retain their written order.  The Björk files become aliases and
remain import-compatible, so there is one declaration home for each result.

## Checks

The package consumer is `AlgebraicAnalysisTest.lean`; the downstream
integration checks are:

```text
lake build AlgebraicAnalysis AlgebraicAnalysisTest
lake env lean --trust=0 AlgebraicAnalysisTest.lean
lake build Bjork
lake env lean --trust=0 research/AxiomAudit.lean
```

The package and Björk axiom audits must contain only the ordinary Lean/Mathlib
foundations, together with Björk's separately declared literature inputs.
