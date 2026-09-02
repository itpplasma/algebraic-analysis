# Agent rules

- `PLAN.md` is the sole current plan.
- The active gate is `NEXT-SLICE-AUDIT`. The Ore/PBW/tower, right-ideal,
  localization, rank, denominator, unimodular-splitting, and projective-image
  slices, plus inverse-Euler/Riccati commutator identities, have passed
  package build and API tests; the module layer is
  currently a private single-consumer layer pending further API review.
- This repository owns reusable, application-independent, axiom-clean
  mathematics. Stafford- or Björk-specific assembly remains downstream.
- A literature theorem is not a trusted fact until proved in Lean. Definitions
  and conditional consumers may record exact interfaces without project axioms.
- Every extraction records source repository, commit, original path, license,
  authorship, declaration mapping, and downstream consumers.
- An extracted declaration has one authoritative home. Remove downstream
  copies in the same integration wave.
- Follow Mathlib naming, documentation, import, and sidedness conventions.
- Tests require an independent behavioral or API oracle; merely matching the
  patch is not a test.
- Preserve unrelated changes and stage explicit paths.
- Keep the repository private until an explicit history, license, secret, and
  release audit passes.
