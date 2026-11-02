module

public import AlgebraicAnalysis.Filtration.SymbolDomain
public import AlgebraicAnalysis.Weyl.BernsteinSymbol

@[expose] public section

/-!
# The Weyl algebra is a domain

For every field `k` (of any characteristic) and every `n`, the Weyl algebra
`A_n(k)` is a domain. The Bernstein symbol identifies the associated graded
ring of the Bernstein filtration with the polynomial ring `k[x, ∂]`, which is
a domain with `1` of degree `0`; `RingFiltration.GradedSymbol.isDomain` lifts
this to `A_n(k)`.
-/

namespace AlgebraicAnalysis.Weyl

variable (k : Type*) [Field k] (n : ℕ)

/-- **The Weyl algebra has no zero divisors**: the product of two nonzero
elements of `A_n(k)` is nonzero. -/
theorem noZeroDivisors : NoZeroDivisors (WeylAlg k n) :=
  (BernsteinSymbol.symbol k n).noZeroDivisors

/-- **The Weyl algebra `A_n(k)` is a domain**, for every field `k`. -/
instance isDomain : IsDomain (WeylAlg k n) :=
  (BernsteinSymbol.symbol k n).isDomain (MvPolynomial.isWeightedHomogeneous_one k _)

end AlgebraicAnalysis.Weyl
