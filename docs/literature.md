# Literature and module index

AlgebraicAnalysis supplies reusable proved algebra to the Stafford38 and
Global Stafford formalizations. Literature explains the mathematical ancestry;
[extraction provenance](provenance.yaml) records where the Lean code came from.
Those are different records. The exact types keep coefficient rings,
sidedness, finiteness and localization hypotheses visible.

## Sources mapped to modules

| Mathematical layer | Context and scope | Lean entry points |
| --- | --- | --- |
| Derivation Ore extensions and PBW normal forms | [Ore33](#ore33); implemented derivation case with ordered coefficients | [RightDivision](../AlgebraicAnalysis/Ore/RightDivision.lean), [RightPBW](../AlgebraicAnalysis/Ore/RightPBW.lean), [IteratedPBW](../AlgebraicAnalysis/Ore/IteratedPBW.lean), [RightHilbertBasis](../AlgebraicAnalysis/Ore/RightHilbertBasis.lean) |
| Right localization and denominator clearance | Ore framework; explicit right denominators and hypotheses | [RightLocalization](../AlgebraicAnalysis/Ore/RightLocalization.lean), [DenominatorTorsion](../AlgebraicAnalysis/Module/DenominatorTorsion.lean) |
| Intrinsic differential operators | [StacksD](#stacksd); recursive commutators | [Basic](../AlgebraicAnalysis/DifferentialOperators/Basic.lean), [CoordinateGeneration](../AlgebraicAnalysis/DifferentialOperators/CoordinateGeneration.lean) |
| Filtered modules and support | [HTT08](#htt08) for context; generic exact algebra implemented here | [FilteredTwoTermPages](../AlgebraicAnalysis/Module/FilteredTwoTermPages.lean), [TwoTermPageLength](../AlgebraicAnalysis/Module/TwoTermPageLength.lean), [EndomorphismKernelSupport](../AlgebraicAnalysis/Module/EndomorphismKernelSupport.lean) |
| Same-divisor identity transport | Source problem [Sta78](#sta78); this library proves conditional transport, not the universal Weyl theorem | [TwoGeneratorIdentity](../AlgebraicAnalysis/RingTheory/TwoGeneratorIdentity.lean) |
| Stable freeness and Ore localization interfaces | Definitions with explicit assumptions; no cited existence theorem supplied | [StablyFree](../AlgebraicAnalysis/Module/StablyFree.lean), [LocalizationExtension](../AlgebraicAnalysis/Ore/LocalizationExtension.lean), [interface review](extraction-review-literature-interfaces.md) |
| Function fields and homogeneous relations | Generic commutative algebra; project extraction records give exact scope | [FunctionField](../AlgebraicAnalysis/FieldTheory/FunctionField.lean), [DistinguishedVariable](../AlgebraicAnalysis/Polynomial/DistinguishedVariable.lean) |
| Commutator and module certificate primitives | Project algebra with all input relations retained | [CommutatorRiccati](../AlgebraicAnalysis/CommutatorRiccati.lean), [EscapeAssembly](../AlgebraicAnalysis/Module/EscapeAssembly.lean), [FilteredSchreyer](../AlgebraicAnalysis/Module/FilteredSchreyer.lean) |

## Downstream proof maps

- [Stafford38 literature and proof map](https://github.com/itpplasma/stafford38-formal/blob/main/docs/literature.md): Weyl Conjecture 3.8, involutivity, visible frames and the exact-degree certificate.
- [Global Stafford literature and proof map](https://github.com/itpplasma/global-stafford-formal/blob/main/docs/literature.md): étale charts, central scalar extension and finite-cover descent.

These are mathematical applications, not dependencies of this library.
Mathlib is pinned in [the manifest](../lake-manifest.json); downstream manifests
choose immutable library revisions. See [release history](release-history.md)
for the versions consumed in recorded verification runs.

## Bibliography

<a id="ore33"></a>

**[Ore33]** Øystein Ore, *[Theory of Non-Commutative Polynomials](https://doi.org/10.2307/1968173)*, Annals of Mathematics (2) 34 (1933), no. 3, 480–508.

Historical foundation for skew polynomial rings. The library implements the derivation case with explicit coefficient order, rather than all skew-polynomial generality.

<a id="stacksd"></a>

**[StacksD]** The Stacks Project Authors, *[Finite order differential operators](https://stacks.math.columbia.edu/tag/09CH)*, The Stacks Project, Section 10.133, tag 09CH (accessed 2026-09-09).

Background for the recursive commutator definition and localization of finite-order differential operators; Lean implementations and hypotheses are indexed below.

<a id="htt08"></a>

**[HTT08]** Ryoshi Hotta, Kiyoshi Takeuchi, and Toshiyuki Tanisaki, *[D-Modules, Perverse Sheaves, and Representation Theory](https://doi.org/10.1007/978-0-8176-4523-6)*, Progress in Mathematics 236, Birkhäuser, 2008.

Background for differential operators, good filtrations and characteristic varieties (Chapters 1–2). No claim of a line-by-line formalization of this book.

<a id="sta78"></a>

**[Sta78]** J. T. Stafford, *[Module Structure of Weyl Algebras](https://doi.org/10.1112/jlms/s2-18.3.429)*, Journal of the London Mathematical Society (2) 18 (1978), 429–442.

Source of Conjecture 3.8 (p. 438). The 1978 conjecture is the target, not a proof of its general case.
