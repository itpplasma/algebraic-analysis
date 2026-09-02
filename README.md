# AlgebraicAnalysis

Reusable Lean foundations for Ore and Weyl algebras, filtered rings and
modules, algebraic differential operators, characteristic geometry, and
related exact certificates.

The repository is private and pre-release. It contains the reviewed
Ore/PBW/tower foundations shared by Stafford38 and Björk, plus generic
right-ideal primitives extracted from Björk: finite right-Ore intersections
and the minimal-degree/principal-right-ideal stage. It also contains the
application-independent Ore-localization, localized rank, split-rank,
denominator-torsion, finite-filtration, unimodular-splitting, and
projective-image primitives used by Björk, together with generic
inverse-Euler/Riccati commutator identities used by Stafford38. Current
pins, provenance, and the distinction between shared and single-consumer
slices are recorded in `PLAN.md` and `docs/provenance.yaml`.

A staged private slice adds the generic central-coordinate escape kernel,
finite-tuple span consequences, and right-coordinate module primitives. The
concrete Ore transport and application-specific correction assemblies remain
in Björk until their integration audit is complete.

The package also exposes the ring/module-only filtered Schreyer equivalence
used to translate a lower-order right-ideal problem into a source relation;
the Stafford-specific presentation and its strictness hypothesis remain in
Stafford38.

Planned downstream consumers:

- `itpplasma/stafford38`;
- `plasma/proj/bjork`;
- selected formal certificate layers from GhostTask.

No theorem from the literature is treated as an axiomatically established
fact. A theorem enters the public API only with an axiom-clean Lean proof.

## Build

```sh
lake exe cache get
lake build
lake test
lake lint
```

On macOS hosts where a cached `runLinter` executable predates the host dyld
format, run the same linter from Lean source:

```sh
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean AlgebraicAnalysis
```
