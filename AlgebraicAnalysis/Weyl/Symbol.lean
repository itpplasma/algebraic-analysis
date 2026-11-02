module
public import Mathlib.Algebra.MvPolynomial.Basic
public import AlgebraicAnalysis.Weyl.Presentation

@[expose] public section

/-!
# Symbol ring of the Weyl algebra

The commutative symbol ring of `A_n(k)`: polynomials in the `2n` phase
variables `x_i` (fibre weight `0`) and `∂_i` (fibre weight `1`).

Provenance: `SymbolRing` and `fibreWeight` are copied from
`Stafford38/Characteristic/Polynomial.lean` of `itpplasma/stafford38-formal` at
commit `ac20b730fb368786e840320ebf6e62d19bbe29f3` (Apache-2.0). The
Poisson bracket and characteristic-support definitions of that file are not
part of this extraction.
-/

namespace AlgebraicAnalysis.Weyl

/-- Coordinate ring of the affine phase space. -/
abbrev SymbolRing (k : Type*) [CommRing k] (n : ℕ) :=
  MvPolynomial (PhaseVar n) k

/-- Fibre degree: base variables have weight zero and covariables weight one. -/
def fibreWeight {n : ℕ} : PhaseVar n → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

end AlgebraicAnalysis.Weyl
