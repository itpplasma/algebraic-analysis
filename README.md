# AlgebraicAnalysis

A Lean 4 library of reusable, application-independent results on Ore and Weyl
algebras, filtered rings and modules, algebraic differential operators and
related commutative algebra. It is the shared foundation of the Stafford
formalizations ([stafford38-formal](https://github.com/itpplasma/stafford38-formal),
[global-stafford-formal](https://github.com/itpplasma/global-stafford-formal)).

Status: research library; declarations may still move or be renamed.

## Contents

- Ore extensions by a derivation: PBW bases, towers, right division,
  principal and intersected right ideals, Ore localization.
- Finite-order differential operators and their localization.
- Filtered modules: two-term filtered complexes, Schreyer-type equivalence,
  support, finite length and minimal-prime localization arguments.
- Filtered rings: associated graded pieces, good filtrations, Hilbert
  functions and Gelfand-Kirillov dimension (the polynomial ring in `n`
  variables has GK dimension exactly `n`).
- `HessianAlgebra`: polynomial self-maps, formal derivatives, affine and
  triangular inverses, Hessians and homogeneous support.
- Smaller pieces on Laurent and power series, rational functions, field
  theory (finite generation of fraction fields) and linear algebra.

A more detailed tour, with module paths, is in [docs/contents.md](docs/contents.md).

The library contains no `sorry` and no `axiom` declarations. Hypotheses are
explicit at each theorem. One notable statement is not proved:
`AlgebraicAnalysis.GKDimension.BernsteinInequality` (in
`AlgebraicAnalysis/Filtration/GKDimension.lean`) is a `Prop`-valued
definition stating the Bernstein inequality over fields of characteristic
zero; it is the open target of the filtration layer and is not used as an
assumption anywhere.

## Building

Requires [elan](https://github.com/leanprover/elan). `lean-toolchain` pins
`leanprover/lean4:v4.35.0-rc3`; `lakefile.toml` pins Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`.

```sh
lake exe cache get
lake build          # AlgebraicAnalysis
lake test           # AlgebraicAnalysisTest
lake lint
```

To use it from another Lake project, add it as a dependency at a fixed
revision, as the downstream projects do:

```toml
[[require]]
name = "algebraicAnalysis"
git = "https://github.com/itpplasma/algebraic-analysis.git"
rev = "<commit>"
```

On macOS, if a cached `runLinter` executable fails to load, run the linter
from source instead:

```sh
lake env lean --run .lake/packages/batteries/scripts/runLinter.lean AlgebraicAnalysis
```

## Documentation

- [docs/contents.md](docs/contents.md): what is in each part of the library.
- [docs/literature.md](docs/literature.md): literature sources and the Lean
  modules that implement them.
- [docs/provenance.yaml](docs/provenance.yaml): origin of extracted
  declarations and downstream consumers.
- [docs/release-history.md](docs/release-history.md): releases and the pins
  used by downstream projects; verification records for v0.3.3 are in
  [docs/verification/v0.3.3](docs/verification/v0.3.3).

## Citing and license

Citation metadata is in [CITATION.cff](CITATION.cff); the latest archived
release is v0.3.3 ([10.5281/zenodo.23104842](https://doi.org/10.5281/zenodo.23104842)).
Licensed under Apache-2.0 ([LICENSE](LICENSE), [NOTICE](NOTICE)).
