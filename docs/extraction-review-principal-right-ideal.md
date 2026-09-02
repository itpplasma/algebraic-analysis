# Extraction review: principal right ideals in a derivation Ore ring

## Scope

This review covers the generic declarations formerly held in
`Bjork/OreIdealDegree.lean` and `Bjork/OreEuclideanPID.lean` at source revision
`c1ff997582bb9a3b9e3c1c78c54090bcb9a8ab9e`. The extracted scope is the
minimal-degree coefficient lemmas, monic-minimum lemmas, transported right
division, and the one-sided principal-right-ideal theorem.

The target is
`AlgebraicAnalysis/Ore/PrincipalRightIdeal.lean`, under
`AlgebraicAnalysis.OrePrincipalRightIdeal`. Björk retains the historical
module names as import-only compatibility wrappers.

## Boundary decision

The declarations quantify only over a division ring, an additive derivation
of its coefficient ring, the coefficient-left Ore normal form, and right
submodules or two-sided ideals of that normal form. They do not mention a
variety, a Weyl presentation, localization, or either headline conjecture.
The coefficient ring remains allowed to be noncommutative.

The right orientation is part of the API: the divisor is on the left and the
quotient on the right, and right ideals are left modules over the opposite
ring. No left-PID statement is introduced.

## Integration evidence

- `AlgebraicAnalysis/Ore/PrincipalRightIdeal.lean` is the sole
  implementation;
- `Bjork/OreIdealDegree.lean` and `Bjork/OreEuclideanPID.lean` contain only
  compatibility declarations;
- Björk's `OreOuterSimple` and `StageT5` retain their historical imports and
  use the extracted declarations;
- `AlgebraicAnalysisTest.lean` instantiates right division and principality
  for the zero derivation over `ℚ`;
- package and downstream trust-zero builds are required before promotion.

The present application consumer is Björk. Stafford38 is deliberately not
made to import this layer without a genuine use. This is a reusable private
package extraction, not a claim about Stafford 3.8 or Björk's global
two-generator conjecture.
