# Hyperplane-restriction extraction review

`AlgebraicAnalysis/Module/HyperplaneRestriction.lean` owns the generic
commutative-algebra kernel formerly declared in Stafford38. It proves that
surjective multiplication by a scalar makes degree-zero restriction vanish
and, for a finite module, forces support to avoid the scalar's principal zero
locus by Nakayama's determinant trick.

The extraction excludes filtered strictness, D-module inverse image,
characteristic varieties, and the Stafford quotient. The Stafford source path
becomes import-only, and concrete consumers open the package namespace.

Promotion requires the package build and API test, a `--trust=0` replay with
no project axiom or `sorry`, and the Stafford consumer and root builds at the
pinned package revision.
