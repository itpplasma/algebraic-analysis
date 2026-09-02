# Extraction review: escape and right-coordinate primitives

Status: staged for integration.

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
products retain written right-sided order.  Björk compatibility files will
become aliases after the package revision is pinned.

## Checks

Before promotion, run the package build and API consumer, the Björk build,
and its trust-zero axiom audit.  The source and compatibility surfaces must
have identical theorem behavior under trust-zero replay, and the package must
introduce no project-specific axioms.
