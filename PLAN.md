# AlgebraicAnalysis: live plan

```yaml
phase: private-package-extraction
mission: reusable-trust-zero-algebraic-analysis
active_gate: next-slice-selection
integrated_api_revision: deae322ac2adcccda37ba84c98b972ef873a2d71
staged_slice: ore-active-coordinate
consumers: [Stafford38, Bjork]
public_release: false
reservoir: false
```

## Mission and boundary

Provide a small Lean package for reusable, application-independent mathematics
used by algebraic-analysis projects. The package owns definitions and proofs
that are useful beyond one paper; Stafford38 and Björk own their headline
claims, literature inputs, geometric/defect assemblies, and research history.

```text
Mathlib -> AlgebraicAnalysis -> Stafford38
                              \\-> Bjork
```

An extracted declaration has one authoritative home. Compatibility modules in
consumers may preserve historical imports, but must not redeclare the API.
The package has no project axioms and no unpublished theorem hidden behind an
opaque declaration.

## Integrated slices

The following foundational slices are complete, audited with `--trust=0`, and
consumed by both downstream repositories at the pinned API revision:

1. derivation-Ore definitions, associativity, normal forms, right quotient,
   and right Hilbert-basis/Noetherian infrastructure;
2. left/right PBW bases and finite commuting Ore towers;
3. the common ring-commutator definition and product/power identities.

The package also contains two generic right-ideal slices extracted from
Björk. They are audited and consumed by Björk; Stafford38 does not import them
merely to manufacture a second consumer:

4. the explicit common-right-multiple criterion and finite right-ideal
   intersection theorem;
5. the minimal-degree and right-principal-ideal stage for derivation Ore
   normal forms over division rings.

The current Björk-only module layer is also extracted and audited:

6. generic Ore-localization fraction, denominator, and full-fraction-ring
   unit facts;
7. division-ring rank, localized right-module torsion, and split rank
   additivity;
8. explicit denominator clearance, finite common annihilators, and finite
   filtration composition.
9. unimodular elements, free rank-one splitting, finite iteration of such
   splittings, and the terminal projective-image factorization.
10. inverse-Euler/Riccati identities for a Weyl-type relation and its
    factorial commutator tower.
11. the ring/module-only filtered Schreyer equivalence, with explicit
    opposite-ring right multiplication and a separately stated strictness
    hypothesis.

The generic noncommutative derivation/centrality kernel, module splice lemmas,
and abstract two-simplicity transfer are integrated at the pinned revision
above.  Their Björk source paths are now import-only compatibility surfaces;
the application-specific hypotheses and assemblies remain in Björk.

The generic central-coordinate escape kernel, finite-tuple escape span, finite
right-coordinate model, and their explicit right-sided module consequences
are integrated at the pinned revision above.  Björk imports them through
compatibility aliases; concrete Ore transport and application-specific
correction assemblies remain downstream.

The next staged slice is the active-coordinate Ore interface from Björk's
twist decomposition.  It packages central-coordinate data, the differential
Ore relation, finite normal-form expansions, and the coefficient commutation
needed by the source-relative tower argument.  It is algebraic and
application-independent, but currently has only Björk as a substantive
consumer; it remains staged until the package and the pinned consumer build
are replayed together.

Provenance and extraction reviews are in
[`docs/provenance.yaml`](docs/provenance.yaml) and
[`docs/extraction-review-ore-pbw.md`](docs/extraction-review-ore-pbw.md).
The staged active-coordinate review is in
[`docs/extraction-review-active-coordinate.md`](docs/extraction-review-active-coordinate.md).
Package API tests and downstream builds are the integration evidence.

## Candidate layers

These are candidates, not promises to extract wholesale:

| Layer | Current disposition |
| --- | --- |
| Ore intersections, division, localization | finite intersection, principal-right-ideal, and generic localization stages are extracted; audit only the remaining application-specific localization/flatness bridge |
| presented Weyl/symplectic substitutions | keep downstream until a second application exists |
| filtrations, Rees, graded and symbol modules | keep downstream while their interfaces are paper-specific; the generic filtered Schreyer criterion is extracted, while its canonical Weyl adapter remains downstream |
| rank, torsion, finite length, unimodular/projective modules | generic division-ring rank, denominator-torsion, unimodular-splitting, and projective-image layers are extracted; finite-length and two-functional/right-sided assemblies remain downstream |
| inverse-Euler/Riccati calculus | generic ring identities are extracted; Weyl-specific applications remain downstream |
| Poisson, Kähler, conormal, DVR and completion | keep theorem-specific until genuinely reusable |
| certificate formats | extract only after a second checker consumes the format |
| central derivation, module splice, two-simplicity transfer | integrated in the package; Björk retains import-only compatibility surfaces and application-specific assemblies |
| central escape and right-coordinate primitives | integrated in the package; concrete Ore transport and escape/splice assemblies remain downstream |

In particular, Björk's noncommutative flatness, rank-to-generator, finite-
length, and unimodular/projective assemblies remain downstream. The extracted
module layer is deliberately conditional and makes no flatness or headline
cyclicity claim. A review record and a second real consumer are required before
the single-consumer layer is promoted beyond private use.

## Integration rules

- pin consumers to an immutable package commit, not to a moving branch;
- keep foundational imports narrow and use neutral `AlgebraicAnalysis` names;
- preserve written-order right-module conventions explicitly;
- require package build, tests, axiom audit, provenance, and consumer builds;
- make one coherent extraction wave at a time and push it as an atomic change;
- keep chronology and failed experiments in repository history, not this file.

## Release gate

Before any public release: deliberate Lean/Mathlib upgrade, Apache-2.0 and
provenance audit, API documentation, Linux/macOS build and test, lint, no
`sorry` or project axioms, downstream examples, and repository/history
privacy and copyright scans. Reservoir remains disabled until explicit
approval.
