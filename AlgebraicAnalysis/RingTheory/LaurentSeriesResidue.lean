import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The residue of a Laurent series

This file records the analytic-free half of the "moment identity" of
`finite-moment-coordinates-all-m.md`, section 1 (`chris/proj/jc2`,
`research/general-pq-carry-20260911/`). That note writes `Res_s H` for the
coefficient `[s^-1] H` of a Laurent series `H`, and uses (as equation (2))
that `Res_s d_s H = 0` because coefficient extraction is linear and the
`s^-1` coefficient of a formal derivative vanishes.

In Mathlib, `LaurentSeries K = HahnSeries ℤ K` (notation `K⸨X⸩`), and this
pinned version of Mathlib already provides the coefficientwise formal
derivative as `LaurentSeries.derivative K : LaurentSeries K →ₗ[K] LaurentSeries K`
(defined as the Hasse derivative of order `1`, `LaurentSeries.hasseDeriv K 1`,
in `Mathlib.RingTheory.LaurentSeries`), satisfying
`(LaurentSeries.derivative K f).coeff n = (n + 1) • f.coeff (n + 1)`
(`LaurentSeries.hasseDeriv_coeff`). No new derivative is defined here.

## Main definitions

* `LaurentSeries.residue`: the `K`-linear map `f ↦ f.coeff (-1)`.

## Main results

* `LaurentSeries.residue_derivative`: `Res_s d_s H = 0`.
* `LaurentSeries.residue_add`, `LaurentSeries.residue_smul`: linearity of the
  residue (`LaurentSeries.residue` is already stated as a `LinearMap`, so
  these are convenience restatements).
* `LaurentSeries.derivative_ofPowerSeries`: for `f` a power series,
  `LaurentSeries.derivative` agrees with `PowerSeries.derivative` under the
  coercion `HahnSeries.ofPowerSeries`.
* `LaurentSeries.derivative_ofPowerSeries_mul`: the Leibniz rule
  `derivative (f * g) = derivative f * g + f * derivative g` for `f g` in the
  image of `HahnSeries.ofPowerSeries`.
-/

namespace AlgebraicAnalysis

variable {K : Type*} [Field K]

/-- The residue of a Laurent series: the coefficient of `s ^ (-1)`, i.e. `Res_s`
of `finite-moment-coordinates-all-m.md`, section 1. -/
noncomputable def LaurentSeries.residue : LaurentSeries K →ₗ[K] K :=
  HahnSeries.coeff.linearMap (-1)

@[simp]
theorem LaurentSeries.residue_apply (f : LaurentSeries K) :
    LaurentSeries.residue f = f.coeff (-1) :=
  rfl

/-- Equation (2): `Res_s d_s H = 0`. The coefficient of `s ^ (-1)` in a formal
derivative is `Ring.choose 0 1 • f.coeff 0 = 0 • f.coeff 0 = 0`. -/
@[simp]
theorem LaurentSeries.residue_derivative (f : LaurentSeries K) :
    LaurentSeries.residue (LaurentSeries.derivative K f) = 0 := by
  rw [LaurentSeries.residue_apply, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff]
  norm_num [Ring.choose_one_right]

theorem LaurentSeries.residue_add (f g : LaurentSeries K) :
    LaurentSeries.residue (f + g) = LaurentSeries.residue f + LaurentSeries.residue g :=
  map_add _ f g

theorem LaurentSeries.residue_smul (c : K) (f : LaurentSeries K) :
    LaurentSeries.residue (c • f) = c * LaurentSeries.residue f := by
  rw [map_smul, smul_eq_mul]

theorem LaurentSeries.residue_sub (f g : LaurentSeries K) :
    LaurentSeries.residue (f - g) = LaurentSeries.residue f - LaurentSeries.residue g :=
  map_sub _ f g

/-- A power series has no coefficients at negative index once coerced into
Laurent series. -/
theorem LaurentSeries.ofPowerSeries_coeff_of_neg (f : PowerSeries K) {n : ℤ} (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ K f).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨m, hm⟩
  simp only [Nat.castOrderEmbedding_apply] at hm
  omega

/-- The `LaurentSeries` formal derivative agrees, under the coercion
`HahnSeries.ofPowerSeries`, with `PowerSeries.derivative`. Both compute the
coefficientwise rule `coeff n ↦ (n + 1) • coeff (n + 1)`; the only content
here is matching up the `ℕ`-indexed and `ℤ`-indexed coefficient conventions,
including that both sides vanish at every negative index. -/
theorem LaurentSeries.derivative_ofPowerSeries (f : PowerSeries K) :
    LaurentSeries.derivative K (HahnSeries.ofPowerSeries ℤ K f) =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.derivative K f) := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff]
  simp only [Nat.cast_one]
  rcases lt_or_ge n 0 with hn | hn
  · rw [LaurentSeries.ofPowerSeries_coeff_of_neg (PowerSeries.derivative K f) hn]
    rcases eq_or_lt_of_le (by omega : n + 1 ≤ 0) with h1 | h1
    · rw [h1]
      simp
    · rw [LaurentSeries.ofPowerSeries_coeff_of_neg f h1, smul_zero]
  · lift n to ℕ using hn with m
    have h1 : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      Ring.choose_one_right, PowerSeries.coeff_derivative, zsmul_eq_mul]
    push_cast
    ring

/-- The Leibniz rule for `LaurentSeries.derivative`, restricted to Laurent
series coming from power series (the hypothesis under which equation (1) of
`finite-moment-coordinates-all-m.md` is used with `F, G` polynomials). Follows
from `LaurentSeries.derivative_ofPowerSeries` and the Leibniz rule for
`PowerSeries.derivative`. -/
theorem LaurentSeries.derivative_ofPowerSeries_mul (f g : PowerSeries K) :
    LaurentSeries.derivative K
        (HahnSeries.ofPowerSeries ℤ K f * HahnSeries.ofPowerSeries ℤ K g) =
      LaurentSeries.derivative K (HahnSeries.ofPowerSeries ℤ K f) *
          HahnSeries.ofPowerSeries ℤ K g +
        HahnSeries.ofPowerSeries ℤ K f *
          LaurentSeries.derivative K (HahnSeries.ofPowerSeries ℤ K g) := by
  rw [← map_mul, LaurentSeries.derivative_ofPowerSeries, LaurentSeries.derivative_ofPowerSeries,
    LaurentSeries.derivative_ofPowerSeries, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    map_add, map_mul, map_mul]
  ring

end AlgebraicAnalysis
