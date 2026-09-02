# Extraction review: finite right-Ore intersections

## Scope

This review covers `Bjork/OreIntersection.lean` at source revision
`4bcc4b6368e64afa9224ba75afa153daef3ab0b7`.  The source contains only the
explicit common-right-multiple predicate and its finite-family right-ideal
intersection theorem.

## Boundary decision

The declarations quantify over a ring, its opposite-ring right-module
encoding, a finite index set, and an explicit right Ore condition.  They do
not mention a Weyl algebra, a geometric space, localization implementation,
or either headline conjecture.  They therefore belong in
`AlgebraicAnalysis.OreRightIntersection`.

The package preserves the source's one-sided conventions: a right ideal is a
left `Rᵐᵒᵖ`-submodule, and the common multiple is written `a * x = b * y`.
No left-Ore or localization conclusion is added.

## Integration evidence

- `AlgebraicAnalysis/Ore/RightIntersection.lean` is the authoritative
  implementation;
- `Bjork/OreIntersection.lean` is now an import-only compatibility surface;
- Björk's existing `EscapeSplice`, `TriangularDenominator`, and related
  consumers continue to use the historical names;
- `AlgebraicAnalysisTest.lean` exercises the API on the integer domain with a
  finite family;
- package build, package test, and the trust-zero source audit pass.

This extraction is an API result only.  It proves neither Stafford 3.8 nor
Björk's two-generator conjecture, and it says nothing about noncommutative
localization exactness.
