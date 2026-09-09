# Extraction review: polynomial-map calculus

## Scope

This review covers `HessianAlgebra/PolynomialMap.lean` in
`itpplasma/hc6-formal` at source revision
`a8face8074577b7455bd577b33f3b8286ce75ca9`. The targets retain their
`AlgebraicAnalysis/HessianAlgebra/*.lean` paths inside the common package while
retaining declaration names in `HessianAlgebra`, so existing theorem names do
not change. Downstream source imports must use the common-package module paths.

The extracted declarations are polynomial substitution and partial
derivatives, gradients and Hessians, polynomial two-sided inverses, the
polynomial Legendre transform, the substitution chain rule, commutation of
partial derivatives, and the Legendre-gradient identity.

## Boundary decision

The module quantifies over an arbitrary field and finite variable type and
imports only Mathlib. It contains no H6 dimension bound, Keller hypothesis,
rank classification, apolar argument, or frontier theorem. It is therefore a
neutral common-library module.

The dependency-closed neutral slice consists of `PolynomialMap`,
`DerivativeKernel`, `AffineInverse`, `CoordinateChange`,
`HessianCoordinateChange`, `TriangularInverse`, `ConstantHessian`,
`HomogeneousDifferential`, `HomogeneousSubstitution`, and
`HomogeneousSupport`. Until the downstream integration wave removes the HC6
providers, this common-package copy is a migration candidate rather than the
authoritative published home.

## License, authorship, and consumers

The source repository and this package are Apache-2.0. Git history attributes
the source module to Christopher Albert. Known consumers are
`itpplasma/hc6-formal`, `itpplasma/hc4-formal`, `itpplasma/jc2-formal`, and
`itpplasma/dc2-formal`.

## Evidence and promotion gate

- all ten extracted modules and both package roots must build against the
  pinned Mathlib;
- the package test instantiates substitution, differentiation, Hessian
  calculation, affine inversion, and homogeneous substitution on concrete
  rational polynomials;
- the downstream integration wave must replace the HC6 source body with an
  import-only compatibility module before calling the package authoritative;
- all downstream consumers must build after advancing their package pin.
