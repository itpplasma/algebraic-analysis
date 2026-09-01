# AlgebraicAnalysis plan

```yaml
phase: private-package-extraction
active_gate: SECOND-SLICE-INTEGRATED
first_consumers: [Stafford38, Bjork]
repository_head: a7276f5232a9deb6f197e259fd8a1188473a636a
integrated_api_revision: 9903c91ea8b89b0f82e3dc17b735911f68adba1c
consumer_heads: Stafford38@3e998dd7198316ee3deb5cb96616f20766723bb4; Bjork@e54deab23b663188fda277994eef95ed0131886e
consumer_state: first and second slices integrated; both consumers build cleanly
public_release: false
reservoir: false
```

## Mission

Provide a stable Lean package for reusable mathematics in algebraic analysis:
Ore extensions, Weyl algebras, filtered/Rees/graded constructions, module and
localization theory, D-module foundations, Poisson and conormal geometry, and
small exact certificate semantics.

The package boundary follows reuse, not novelty. Canonical literature results
and new general lemmas may both belong here when they have axiom-clean proofs
and application-independent statements. Headline paper theorems and their
specific assembly remain downstream.

## Active gate

`stafford38` has completed the inventory and both reviewed Ore/PBW consumer
migrations. The remaining cleanup gate is upstream in Stafford38; this package
stabilizes the extracted API and provenance. Do not copy either project
wholesale, create generalized wrappers for unstable proof-specific modules, or
import unpublished claims as axioms or trusted opaque declarations.

## First extraction slice

The initial vertical slice is already consumed by both Stafford38 and Björk.
The second slice is also integrated. The consumers deliberately pin the
immutable API revision above; the package repository head currently contains
provenance synchronization after that integration wave:

```text
derivation-Ore definitions
  -> associativity
  -> normal form and PBW
  -> right Hilbert-basis/Noetherian theorem
```

The slice is `FORMALIZED`: its declarations have a trust-zero audit with only
the standard Lean/Mathlib foundation. This does not formalize literature
inputs or theorem-specific bridges in the consumer repositories. Consumers
keep those inputs as explicit hypotheses; this package exposes no project
axioms for them.

Success requires:

1. neutral `AlgebraicAnalysis` names and documentation;
2. provenance for every extracted declaration;
3. trust-zero build, axiom audit, external API consumers, and behavioral
   oracles where computation is meaningful;
4. Stafford38 and Björk both building against one pinned library revision;
5. removal of the extracted downstream copies in the same integration wave.

## Second extraction slice: PBW and commuting Ore towers

The reviewed second slice is integrated and pinned by both consumers. It moves
the application-independent material
from Björk commit `414131f` into five neutral modules:

```text
LeftPBW -> Tower -> IteratedTower -> IteratedPBW
RightPBW
```

The package build, API tests, and both consumer builds pass with the standard
Lean foundation only. The consumers retain only import-only compatibility
modules at the old paths. The package owns no Stafford/Björk theorem, no
literature assumption, and no project-specific bridge.

The boundary review is recorded in
`docs/extraction-review-ore-pbw.md`; declaration provenance is recorded in
`docs/provenance.yaml`.

## Later candidate layers

1. Ore intersections, division, and localization;
2. universal/presented Weyl algebras and symplectic substitutions;
3. filtrations, Rees objects, associated graded modules, and symbols;
4. rank, torsion, finite length, unimodular and projective modules;
5. characteristic support, Poisson, Kähler, conormal, DVR, and completion;
6. Lean-level certificate formats shared with GhostTask.

Candidates remain downstream until their API is stable or a second consumer
demonstrates reuse. Stafford's canonical quotient, Euler proof assembly,
equation-(3.3), and final certificate stay in Stafford38. Named Björk relative
theorems and defect absorption stay in Bjork.

## Release gate

- Apache-2.0 licensing and complete provenance audit;
- current stable Lean/Mathlib pin reached by deliberate upgrade steps;
- narrow imports and Mathlib naming conventions;
- `autoImplicit false` in foundational modules;
- `lake build`, `lake test`, and `lake lint` on Linux and macOS;
- no `sorry`, project axioms, or opaque load-bearing declarations;
- generated API documentation and downstream examples;
- complete repository and Git-history privacy/copyright scan;
- Reservoir remains disabled until explicit public-release approval.
