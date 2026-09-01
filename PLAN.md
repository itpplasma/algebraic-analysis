# AlgebraicAnalysis plan

```yaml
phase: private-package-bootstrap
active_gate: WAIT-STAFFORD38-CLEAN
first_consumers: [Stafford38, Bjork]
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

Do not extract source files yet. `stafford38` first completes
`STAFFORD38-CLEAN`: one authoritative active Lean tree, an exact root/checker
closure, removal of obsolete current-tree copies, and a machine-readable
classification of modules.

During this gate:

- maintain only the package skeleton and extraction contract;
- do not copy the Stafford or Björk trees wholesale;
- do not create generalized wrappers for unstable proof-specific modules;
- do not import unpublished claims as axioms or trusted opaque declarations.

## First extraction slice

The initial vertical slice is already consumed by both Stafford38 and Björk:

```text
derivation-Ore definitions
  -> associativity
  -> normal form and PBW
  -> right Hilbert-basis/Noetherian theorem
```

Success requires:

1. neutral `AlgebraicAnalysis` names and documentation;
2. provenance for every extracted declaration;
3. trust-zero build, axiom audit, external API consumers, and behavioral
   oracles where computation is meaningful;
4. Stafford38 and Björk both building against one pinned library revision;
5. removal of the extracted downstream copies in the same integration wave.

## Later candidate layers

1. iterated Ore towers, division, localization, and PBW bases;
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

