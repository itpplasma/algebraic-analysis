# Extraction review: active-coordinate Ore interface

## Scope

This review covers `Bjork/TwistDecomposition.lean` at source revision
`da5610624626bfdbb9a5003f85be308563d579dc7`. The target is
`AlgebraicAnalysis/Ore/ActiveCoordinate.lean` under the namespace
`AlgebraicAnalysis.OreActiveCoordinate`.

The extracted declarations are:

- `ActiveCoordinateData`;
- `coefficient`, `activeVariable`, and `coordinatePolynomial`;
- the active-variable relation and scalar commutation lemmas;
- coefficient/coordinate-polynomial commutation;
- the finite normal-form expansion;
- `recombine_coordinate_polynomial`;
- `exists_active_expansion`.

## Boundary decision

The source quantifies only over a commutative ground ring, a ring of
coefficients, an algebra structure, a derivation-Ore normal form, and explicit
centrality/derivation hypotheses. It mentions no Weyl presentation, concrete
operator ring, right ideal, localization, Stafford statement, Björk defect, or
literature input. It is therefore suitable for the reusable package.

The package owns the declarations. `Bjork/TwistDecomposition.lean` is now an
import-only compatibility path, and `ConcreteTwistDecomposition.lean` names
the package namespace explicitly. No second theorem body or alias namespace is
kept in Björk.

The package deliberately preserves the source-relative hypotheses. In
particular, centrality of the distinguished coordinate is not inferred from a
presented Weyl algebra, and normal-form surjectivity is not upgraded to a
global two-generator or Stafford conclusion.

## Evidence and promotion gate

- the package module builds under Lean 4.16/Mathlib v4.16;
- `AlgebraicAnalysisTest.lean` exercises a polynomial-derivation instance and
  both the active relation and expansion theorem;
- the extracted declarations report only the ordinary Lean/Mathlib axioms;
- Björk must build after its package pin is advanced to the commit containing
  this module;
- the provenance record and consumer plan must name the exact revisions.

This is an API extraction result only. It does not close the active Björk
defect-absorption frontier or any Stafford38 open bridge.
