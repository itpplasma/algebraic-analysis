# AlgebraicAnalysis: live plan

```yaml
phase: private-package-extraction
mission: reusable-trust-zero-algebraic-analysis
active_gate: stable-api-and-second-consumer-review
integrated_api_revision: 437c41b8aaefdf3a7043cc2be862cdb443132530
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

Provenance and extraction reviews are in
[`docs/provenance.yaml`](docs/provenance.yaml) and
[`docs/extraction-review-ore-pbw.md`](docs/extraction-review-ore-pbw.md).
Package API tests and downstream builds are the integration evidence.

## Candidate layers

These are candidates, not promises to extract wholesale:

| Layer | Current disposition |
| --- | --- |
| Ore intersections, division, localization | finite intersection and principal-right-ideal stages are extracted; audit the remaining localization layer for a stable generic slice |
| presented Weyl/symplectic substitutions | keep downstream until a second application exists |
| filtrations, Rees, graded and symbol modules | keep downstream while their interfaces are paper-specific |
| rank, torsion, finite length, unimodular/projective modules | audit for independent consumers; no forced migration |
| Poisson, Kähler, conormal, DVR and completion | keep theorem-specific until genuinely reusable |
| certificate formats | extract only after a second checker consumes the format |

In particular, Björk's rank, localization, denominator, and unimodular files
remain downstream: their present APIs are tied to the Björk namespace or have
only one downstream consumer. A review record and a second real consumer are
required before those layers are promoted.

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
