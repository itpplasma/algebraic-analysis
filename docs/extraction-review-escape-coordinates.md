# Extraction review: escape and right-coordinate primitives

Status: integrated.  The package API is authoritative at commit
`b9685539b4c0b80573d4139e196ad28b9b2ec7b0`; Björk consumes that immutable
revision through import-only compatibility surfaces.

## Scope

This slice moves four generic groups from Björk:

- the central-coordinate commutator and polynomial derivative/unit-production
  kernel;
- finite-tuple commutator-span consequences over an opposite-ring module;
- the finite residual-coordinate elimination argument;
- the finitely supported right-coordinate action and pure-coordinate
  decomposition.

The target modules use only explicit ring, division-ring, polynomial, and
module hypotheses.  They contain no Weyl presentation, localization theorem,
characteristic-variety argument, literature input, or final two-generator
claim.

## Boundary audit

The central escape structure takes the PBW normal-form and commutator
transport identity as data.  The finite-tuple theorem separately requires
strictly decreasing polynomial degrees and closure under left multiplication by
the distinguished coordinate.  The right-coordinate file does not encode
freeness of an Ore localization.  These hypotheses remain visible to
downstream concrete files.

All module scalars are actions of the opposite ring, so the displayed
products retain written right-sided order.  Björk compatibility files are
aliases after pinning the package revision.

## Checks

The integration checks completed with:

```text
lake build AlgebraicAnalysis AlgebraicAnalysisTest
lake env lean --trust=0 AlgebraicAnalysisTest.lean
lake build Bjork
research/check_axioms.sh
```

The package introduces no project-specific axioms; the downstream audit
allows only the ordinary Lean foundations and the explicitly declared
literature inputs.
