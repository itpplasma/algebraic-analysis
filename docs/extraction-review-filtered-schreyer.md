# Extraction review: filtered Schreyer criterion

## Boundary

The source theorem is independent of Weyl algebras, Ore extensions, and
characteristic geometry.  It is a precise equivalence for a right-linear
presentation, an additive lower subgroup, and one distinguished right action.
The extracted module retains the opposite-ring encoding of right
multiplication and does not claim that the strictness hypothesis holds for any
particular filtered quotient.

| Source | Target | Scope |
| --- | --- | --- |
| `Stafford38/Characteristic/ExactFilteredSchreyerCriterion.lean` | `AlgebraicAnalysis/Module/FilteredSchreyer.lean` | `map_rightSMul` and `range_add_lower_iff_preimage_add_rightMultiple` |

The original Stafford38 path is now an import-only compatibility surface.  The
canonical two-generator presentation, its Euler cofactor, and the open
strictness producer remain in Stafford38.

## Provenance

- Source repository: `itpplasma/stafford38`
- Source revision: `5fdf5f3c163e5302a72c493cf716842f8c5e2fd4`
- License: Apache-2.0, inherited from the source repository
- Authorship: inherited repository contribution; source history remains in Stafford38
- Current consumer: Stafford38

## Evidence and limits

- The target builds under `lake build` and `--trust=0`.
- The source checker exhaustively tests the finite two-dimensional statement
  over `F₂` and checks a separate signature consumer; that behavioral oracle is
  independent of the Lean proof.
- The reviewed theorem uses right-coordinate stability in the forward
  direction and strictness in the reverse direction.  It does not prove
  filtered strictness, the canonical source membership, or Stafford 3.8.
