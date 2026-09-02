# Extraction review: localization, rank, and denominator layer

## Boundary

This wave extracts the application-independent portions of Björk's reviewed
localization and module handover packet. The source declarations quantify over
general monoids, rings, division rings, Ore sets, right modules, and explicit
finite filtrations. They do not mention varieties, differential operators,
Stafford's theorem, or Björk's global defect assembly.

The extracted targets are:

| Source | Target | Scope |
| --- | --- | --- |
| `Bjork/StageLocalization.lean` | `AlgebraicAnalysis/Ore/Localization.lean` | common denominators, fraction representatives, numerator injection, and unit facts |
| `Bjork/RankTorsion.lean` | `AlgebraicAnalysis/Module/RankTorsion.lean` | division-ring rank and localized right-module torsion criteria |
| `Bjork/RankExact.lean` | `AlgebraicAnalysis/Module/RankExact.lean` | rank additivity from explicit split/product equivalences |
| `Bjork/DenominatorTorsion.lean` | `AlgebraicAnalysis/Module/DenominatorTorsion.lean` | explicit clearance, principal right ideals, and quotient torsion |
| `Bjork/TriangularDenominator.lean` | `AlgebraicAnalysis/Module/TriangularDenominator.lean` | finite common annihilators and finite filtration clearance |

The original Björk paths remain import-only compatibility surfaces. The
package deliberately does not extract Björk's noncommutative flatness gap,
rank-to-generator argument, finite-length selection, or unimodular/projective
defect assembly.

## Provenance

- Source repository: `plasma/proj/bjork`
- Source revision: `2b398f0d8969b552133f33885bceab1988dabdc7`
- License: Apache-2.0, inherited from the source repository
- Authorship: inherited repository contribution; source history remains in
  Björk
- Current application consumer: Björk
- Stafford38 is not imported merely to manufacture a second consumer.

## Evidence

- Each target module builds under Lean 4.16 with the ordinary foundation.
- The package API test instantiates the localization, rank, clearance, and
  filtration interfaces.
- Björk's compatibility modules and full axiom audit are the downstream
  integration checks after the package revision is pinned.
- The declarations make no project-axiom or `sorry` claim; their ordinary
  `propext`, choice, and quotient dependencies are reported by Lean.
