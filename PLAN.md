# AlgebraicAnalysis formal status

Updated 2026-09-12. This repository owns reusable, application-independent
Lean foundations; downstream Stafford, Björk, JC2, and Navier projects own
their application-specific proof assembly.

## Current boundary

- The Ore/PBW, localization, filtered-module, support, rank, and Hessian
  foundations in the public API are proved with ordinary Lean/Mathlib axioms
  only.
- `AlgebraicAnalysis.BernsteinInequality` is statement-only and remains open;
  its field binder now explicitly requires `CharZero K`.
- The pre-repair arbitrary-field statement was false: the first Weyl algebra over
  `𝔽₂` acting on `𝔽₂[t]/(t²)` has a nonzero constant-filtered module of GK
  dimension zero, contradicting the displayed lower bound one. The exact
  independent check is
  `research/bernstein_characteristic_p_oracle.py`.

## Next valid work

Formalize the repaired characteristic-zero Bernstein theorem, including any
remaining nondegeneracy hypotheses required by the proof. Do not add an
application-specific axiom.
The boundary review is recorded in
`docs/review-bernstein-boundary.md`; the public README remains intentionally
short.
