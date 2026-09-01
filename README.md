# AlgebraicAnalysis

Reusable Lean foundations for Ore and Weyl algebras, filtered rings and
modules, algebraic differential operators, characteristic geometry, and
related exact certificates.

The repository is private and pre-release. It currently contains only the
package boundary and build skeleton. Extraction from Stafford38 begins only
after the Stafford cleanup gate in `PLAN.md` is complete.

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
