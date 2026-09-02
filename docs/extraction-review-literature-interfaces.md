# Extraction review: filtered-ring literature interfaces

## Scope

This wave extracts two application-independent interfaces from
`itpplasma/bjork` at revision
`b04ba6310497f7c7b9560ed9ecb395be49c754c3`:

- stable freeness of finitely generated projective right modules;
- localization of a derivation-Ore extension as a derivation-Ore extension
  over the localized coefficient ring.

The package adds no axiom and proves no cited theorem.  The first interface is
a `Prop`; the second is an existence proposition containing the extended
derivation, ring equivalence, and coefficient-embedding compatibility.  A downstream project
may cite literature by assuming that these interfaces are inhabited, without
turning the shared package itself into an axiomatic development.

## Boundary

The localization interface assumes Ore-ness of both the coefficient
denominator set and its image in the Ore extension.  It does not derive the
second condition from derivation stability.  The stable-freeness interface
does not identify a Grothendieck group and supplies no instance for a
differential-operator ring.

## Verification

The package test consumes both public interfaces at their exact types.  Björk
must still build after its package pin is advanced to the commit containing
these modules and its local definition and existential result are replaced by
compatibility aliases to this package.

An independent frozen-patch API audit returned `REPAIR` only because the
first draft described the downstream replay as completed.  That wording was
corrected above.  The reviewer separately checked right-module orientation
and elaborated both directions between the old localization axiom conclusion
and the new proposition; both passed.
