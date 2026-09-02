# Hyperplane-restriction extraction review

`AlgebraicAnalysis/Module/HyperplaneRestriction.lean` owns the generic
commutative-algebra kernel formerly declared in Stafford38. It proves that
surjective multiplication by a scalar makes degree-zero restriction vanish
and, for a finite module, forces support to avoid the scalar's principal zero
locus by Nakayama's determinant trick.

The extraction excludes filtered strictness, D-module inverse image,
characteristic varieties, and the Stafford quotient. The Stafford source path
becomes import-only, and concrete consumers open the package namespace.

Promotion evidence:

- package build, API test, and direct `--trust=0` replay pass;
- the axiom report contains only `propext`, `Classical.choice`, and
  `Quot.sound`;
- an independent semantic comparison found no theorem or proof difference
  beyond namespace and documentation;
- Stafford pins API commit `cac7a66d96392924b952fe1961a867e83e20ff9c`;
- Stafford's focused hyperplane and canonical-axis checks and full root build
  pass at consumer commit `465e29aa16deb228801c1e30e4eb5ef072cc0778`.
