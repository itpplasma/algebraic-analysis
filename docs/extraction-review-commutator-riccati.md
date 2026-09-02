# Extraction review: inverse-Euler/Riccati commutator calculus

## Boundary

The source file is an active Stafford38 compatibility input, but every
declaration is stated over an arbitrary ring. The extracted module contains
the local commutator notation, iterated commutation, the inverse-Euler
identity, the Euler commutator identity, and the factorial tower. It does not
encode a Weyl algebra, a filtration, a module quotient, or Stafford's
conjecture.

| Source | Target | Scope |
| --- | --- | --- |
| `proofs/inverse_euler_riccati.lean` | `AlgebraicAnalysis/CommutatorRiccati.lean` | generic ring commutator/inverse/Euler identities |

The original Stafford38 path remains an import-only compatibility surface.
The Weyl symplectic presentation and pure-power Euler certificate remain in
Stafford38 because they are application-specific.

## Provenance

- Source repository: `itpplasma/stafford38`
- Source revision: `9858d57fd84e208447d940141c52c7511e7ff101`
- License: Apache-2.0, inherited from the source repository
- Authorship: inherited repository contribution; source history remains in
  Stafford38
- Current application consumer: Stafford38

## Evidence and limits

- The target builds with the ordinary Lean foundation and is imported by the
  package root.
- The package API test checks the base cases of the iterated commutator.
- The source checker remains a downstream two-run trust-zero replay after its
  compatibility wrapper is installed.
- The inverse and Weyl-type relations are explicit hypotheses; no inverse or
  universal Stafford certificate is supplied by this module.
