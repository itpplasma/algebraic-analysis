import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Exactness of the Jacobian divergence identity

This file records the pure-algebra half of the "moment identity" used by the
JC2 corner machine, `finite-moment-coordinates-all-m.md`, section 1, equations
(1) and (2) (`chris/proj/jc2`, `research/general-pq-carry-20260911/`). That
note works with `Res_s` of Laurent series in one variable `s` over a
differential base field `C(w)`, with `d_s` and `d_w` the two commuting
derivations. Equation (1) there reads, for `F, G` polynomials and `q`
rational,

  `d_w(G F_s F^q) - d_s(G F_w F^q) = F^q J_(s,w)(F, G)`

where `J_(s,w)(F, G) = F_s G_w - F_w G_s` is the Jacobian. This file states
and proves the underlying commutative-ring identity that makes (1) true,
in the generality of two commuting derivations `ds dw : Derivation ℤ R R`
on any commutative ring `R`, with `F^q` replaced by an arbitrary element
`Φ` satisfying the (necessary and, for `Φ = F^q` formally, sufficient)
compatibility relation `ds Φ * dw F = dw Φ * ds F`.

No fractional or formal power `F^q` for irrational/non-integer `q` is
constructed here; `Φ` is only required to satisfy the algebraic relation
that such a power would satisfy formally. The natural-number power case
`Φ = F ^ k` is recorded as a corollary, where the relation holds
automatically by the Leibniz rule.
-/

namespace AlgebraicAnalysis

variable {R : Type*} [CommRing R]

/-- The pure-algebra core of the moment identity (1) of
`finite-moment-coordinates-all-m.md`, section 1: for two *commuting*
derivations `ds`, `dw` of a commutative ring `R`, and `Φ` satisfying the
compatibility relation `ds Φ * dw F = dw Φ * ds F` that a formal power
`Φ = F ^ q` would satisfy, the "cross divergence" of `G * ds F * Φ` and
`G * dw F * Φ` is exactly `Φ` times the Jacobian `ds F * dw G - dw F * ds G`.

This is the Leibniz expansion of equation (1); no analytic input (residues,
convergence, Laurent series) is used at this level of generality. -/
theorem Derivation.jacobian_exact_of_commute (ds dw : Derivation ℤ R R)
    (hcomm : ∀ x : R, ds (dw x) = dw (ds x)) (F G Φ : R)
    (hΦ : ds Φ * dw F = dw Φ * ds F) :
    dw (G * ds F * Φ) - ds (G * dw F * Φ) =
      Φ * (ds F * dw G - dw F * ds G) := by
  have hw : dw (G * ds F * Φ) =
      G * ds F * dw Φ + Φ * (G * dw (ds F) + ds F * dw G) := by
    rw [Derivation.leibniz, Derivation.leibniz]
    simp only [smul_eq_mul]
  have hs : ds (G * dw F * Φ) =
      G * dw F * ds Φ + Φ * (G * ds (dw F) + dw F * ds G) := by
    rw [Derivation.leibniz, Derivation.leibniz]
    simp only [smul_eq_mul]
  rw [hw, hs, hcomm F]
  linear_combination (-G) * hΦ

/-- Corollary of `Derivation.jacobian_exact_of_commute` for `Φ = F ^ k`, a
natural-number power: the compatibility relation `ds (F ^ k) * dw F =
dw (F ^ k) * ds F` holds automatically by the Leibniz power rule, so no side
hypothesis is needed. This is the integer-`q` case of equation (1). -/
theorem Derivation.jacobian_exact_pow (ds dw : Derivation ℤ R R)
    (hcomm : ∀ x : R, ds (dw x) = dw (ds x)) (F G : R) (k : ℕ) :
    dw (G * ds F * F ^ k) - ds (G * dw F * F ^ k) =
      F ^ k * (ds F * dw G - dw F * ds G) := by
  apply Derivation.jacobian_exact_of_commute ds dw hcomm F G (F ^ k)
  rw [Derivation.leibniz_pow, Derivation.leibniz_pow]
  simp only [smul_eq_mul]
  ring

/-- Corollary of `Derivation.jacobian_exact_of_commute` for `Φ = 1`
(the `q = 0` case of equation (1)): the divergence identity for the bare
products `G * ds F` and `G * dw F`. -/
theorem Derivation.jacobian_exact_one (ds dw : Derivation ℤ R R)
    (hcomm : ∀ x : R, ds (dw x) = dw (ds x)) (F G : R) :
    dw (G * ds F) - ds (G * dw F) = ds F * dw G - dw F * ds G := by
  have := Derivation.jacobian_exact_pow ds dw hcomm F G 0
  simpa using this

end AlgebraicAnalysis
