# Function-field finite-generation review

`top_fg_of_finiteType_fractionRing` is application-independent.  Starting
from a finite algebra-generating set for a domain `A`, it maps that set into a
fraction field `K`.  Algebra-adjoin induction shows that the resulting
intermediate field contains the image of every element of `A`; fraction
surjectivity then shows that it contains every element of `K`.

The statement deliberately concludes `IntermediateField.FG`.  It does not
assert `Algebra.FiniteType k K`, which is false for a nonalgebraic function
field.  The implementation needs only the standard fraction-field and scalar
tower instances and introduces no project axiom.

Independent API evidence is the specialization

```lean
(⊤ : IntermediateField ℚ (FractionRing (Polynomial ℚ))).FG
```

in `AlgebraicAnalysisTest.lean`.  Both the generic source and this concrete
consumer are checked with `--trust=0`; their axiom report is limited to the
ordinary Lean/Mathlib foundation.
