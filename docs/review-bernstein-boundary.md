# Bernstein inequality boundary

`AlgebraicAnalysis.BernsteinInequality` is a statement-only target; it is not
a proved theorem and no public theorem depends on it. Its field binder now
explicitly requires characteristic zero.

The pre-repair quantification over arbitrary fields was false. For `n = 1` over
`𝔽₂`, the first Weyl algebra with its PBW filtration satisfies the displayed
Hilbert-function, commutator-drop, and Weyl-relation hypotheses. The module
`𝔽₂[t]/(t²)` with multiplication and differentiation, equipped with the
constant filtration, is nonzero and finite, so its GK dimension is zero while
the target lower bound is one.

The independent exact check is
`research/bernstein_characteristic_p_oracle.py`. The next valid target must
make the characteristic-zero/nondegeneracy boundary explicit before any proof
attempt is promoted.
