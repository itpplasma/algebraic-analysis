-- SPDX-License-Identifier: Apache-2.0
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Data.EReal.Basic

/-!
# Hilbert functions of filtered modules and their growth degree

Let `K` be a division ring, `M` a `K`-module and `G : ℕ → Submodule K M` an
ascending filtration whose pieces are finite-dimensional.  The *Hilbert
function* of `G` is `hilbertFunction G i = finrank K (G i)`.

This file has two independent halves.

* The **module half** records the two elementary facts about `hilbertFunction`:
  it is monotone, and its first difference is the dimension of the graded piece
  `G (i+1) / G i` (`finrank_gradedPiece_add_hilbertFunction`).

* The **growth half** is about arbitrary functions `h : ℕ → ℕ`.  It defines the
  set `growthExponents h` of real `d ≥ 0` for which `h i` is eventually bounded
  by a constant times `i ^ d`, and the `growthDegree h : EReal` as the infimum of
  that set.  The load-bearing results are `growthExponents_eq_of_shift_squeeze`
  and `growthDegree_eq_of_shift_squeeze`: two functions that dominate each other
  after bounded shifts of the argument have the *same* growth exponents, hence
  the same growth degree.  Applied to Hilbert functions
  (`growthDegree_hilbertFunction_eq_of_bounded_shift`) this is exactly the
  statement that the growth degree does not depend on which of two filtrations
  comparable up to bounded shift is used.

`growthDegree` takes values in `EReal` on purpose: for a function of
superpolynomial growth `growthExponents h` is empty and `growthDegree h = ⊤`.
Collapsing this to a real number would make it indistinguishable from the
bounded case.

## What is assumed and what is not

* No exhaustiveness (`⨆ i, G i = ⊤`) is used anywhere in this file.  Every
  statement about `hilbertFunction G` is a statement about the individual pieces
  `G i` only, so exhaustiveness may be added freely at the point of use.
* No ring acts on `M` beyond `K`; in particular nothing here knows about a
  filtered ring acting compatibly on `M`, about good filtrations, or about
  finite generation of the associated graded module.  The comparison hypotheses
  `G i ≤ G' (i + a)` and `G' i ≤ G (i + b)` in
  `growthDegree_hilbertFunction_eq_of_bounded_shift` are taken as explicit
  hypotheses; this file does not prove that two good filtrations satisfy them.
* Nothing here asserts that a Hilbert function *is* eventually polynomial.
  `growthDegree_eq_natDegree_of_eventually_eq` is a conditional statement whose
  hypotheses are precisely that agreement together with `p ≠ 0`.

## Relation to Mathlib on the pinned revision

The pinned Mathlib has `Polynomial.hilbertPoly p d`
(`Mathlib/RingTheory/Polynomial/HilbertPoly.lean`), the polynomial whose values
are the coefficients of the power series expansion of `p / (1 - X) ^ d` over a
field of characteristic zero, together with `Polynomial.preHilbertPoly`,
`Polynomial.existsUnique_hilbertPoly` and `Polynomial.natDegree_hilbertPoly_of_ne_zero`.
That file's own `TODO` records that Hilbert polynomials of finitely generated
graded modules are absent.  Searching the pin further:

* there is no `Polynomial.IsIntegerValued` and no numerical-polynomial API;
  `Mathlib/RingTheory/Binomial.lean` provides binomial rings and
  `Ring.multichoose`, but not integer-valued polynomials as a subring of `ℚ[X]`
  with the binomial-coefficient basis;
* there is no Hilbert–Serre theorem and no Hilbert series of a graded module;
* there is no Gelfand–Kirillov dimension, and no growth-degree invariant for
  functions `ℕ → ℕ`.

Consequently the growth half below is built directly on `Real.rpow`,
`Filter.atTop` and `Asymptotics`, and reuses `Polynomial.isEquivalent_atTop_lead`
for the single place where a polynomial appears.
-/

namespace AlgebraicAnalysis
namespace HilbertFunction

open Filter Module

/-! ## The Hilbert function of a filtration -/

section Module

variable {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]

/-- The Hilbert function of a filtration `G` of `M` by `K`-subspaces: the
dimension of the `i`-th piece.  No hypothesis on `G` is imposed by the
definition; `finrank` is `0` on pieces that are not finite-dimensional. -/
noncomputable def hilbertFunction (G : ℕ → Submodule K M) (i : ℕ) : ℕ := finrank K (G i)

/-- The `i`-th graded piece `G (i+1) / G i` of a filtration, realised as the
quotient of `G (i+1)` by the copy of `G i` sitting inside it.  This is the same
device as `AlgebraicAnalysis.FilteredStrictness.GradedQuotient`, written with
`Submodule.comap` of the inclusion instead of its range. -/
abbrev gradedPiece (G : ℕ → Submodule K M) (i : ℕ) : Type _ :=
  G (i + 1) ⧸ Submodule.comap (G (i + 1)).subtype (G i)

/-- The Hilbert function of a monotone filtration by finite-dimensional pieces is
monotone. -/
theorem hilbertFunction_mono (G : ℕ → Submodule K M) (hG : Monotone G)
    (hfin : ∀ i, Module.Finite K (G i)) : Monotone (hilbertFunction G) := by
  intro i j hij
  have := hfin j
  exact Submodule.finrank_mono (hG hij)

/-- The first difference of the Hilbert function is the dimension of the graded
piece: `dim (G (i+1) / G i) + h i = h (i+1)`. -/
theorem finrank_gradedPiece_add_hilbertFunction (G : ℕ → Submodule K M) (hG : Monotone G)
    (hfin : ∀ i, Module.Finite K (G i)) (i : ℕ) :
    finrank K (gradedPiece G i) + hilbertFunction G i = hilbertFunction G (i + 1) := by
  have := hfin (i + 1)
  have hle : G i ≤ G (i + 1) := hG (Nat.le_succ i)
  have h1 := Submodule.finrank_quotient_add_finrank
    (R := K) (M := (G (i + 1) : Submodule K M)) (Submodule.comap (G (i + 1)).subtype (G i))
  rwa [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h1

/-- The subtracted form of `finrank_gradedPiece_add_hilbertFunction`. -/
theorem finrank_gradedPiece_eq_sub (G : ℕ → Submodule K M) (hG : Monotone G)
    (hfin : ∀ i, Module.Finite K (G i)) (i : ℕ) :
    finrank K (gradedPiece G i) = hilbertFunction G (i + 1) - hilbertFunction G i := by
  rw [← finrank_gradedPiece_add_hilbertFunction G hG hfin i, Nat.add_sub_cancel]

end Module

/-! ## Growth exponents of a natural-number sequence -/

/-- `d` is a growth exponent of `h` when `d ≥ 0` and `h i` is eventually bounded
by a constant multiple of `i ^ d` (real power). -/
def IsGrowthExponent (h : ℕ → ℕ) (d : ℝ) : Prop :=
  0 ≤ d ∧ ∃ C : ℝ, ∀ᶠ i : ℕ in atTop, (h i : ℝ) ≤ C * (i : ℝ) ^ d

/-- The set of growth exponents of `h`, a subset of `[0, ∞)`. -/
def growthExponents (h : ℕ → ℕ) : Set ℝ := {d | IsGrowthExponent h d}

theorem mem_growthExponents {h : ℕ → ℕ} {d : ℝ} :
    d ∈ growthExponents h ↔ IsGrowthExponent h d := Iff.rfl

theorem growthExponents_subset_Ici (h : ℕ → ℕ) : growthExponents h ⊆ Set.Ici 0 :=
  fun _ hd => Set.mem_Ici.mpr hd.1

/-- A growth exponent can always be witnessed by a nonnegative constant. -/
theorem IsGrowthExponent.exists_nonneg_const {h : ℕ → ℕ} {d : ℝ} (hd : IsGrowthExponent h d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i : ℕ in atTop, (h i : ℝ) ≤ C * (i : ℝ) ^ d := by
  obtain ⟨-, C, hC⟩ := hd
  refine ⟨max C 0, le_max_right _ _, hC.mono fun i hi => hi.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg i) _)

/-- The set of growth exponents is upward closed. -/
theorem IsGrowthExponent.mono {h : ℕ → ℕ} {d d' : ℝ} (hd : IsGrowthExponent h d) (hdd : d ≤ d') :
    IsGrowthExponent h d' := by
  obtain ⟨C, hC0, hC⟩ := hd.exists_nonneg_const
  refine ⟨hd.1.trans hdd, C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with i hi hi1
  refine hi.trans (mul_le_mul_of_nonneg_left ?_ hC0)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hi1) hdd

/-- Domination after a forward shift of the argument transfers growth exponents:
if `h i ≤ g (i + a)` eventually, every growth exponent of `g` is one of `h`. -/
theorem IsGrowthExponent.of_le_add {g h : ℕ → ℕ} {d : ℝ} {a : ℕ}
    (hle : ∀ᶠ i : ℕ in atTop, h i ≤ g (i + a)) (hg : IsGrowthExponent g d) :
    IsGrowthExponent h d := by
  obtain ⟨C, hC0, hC⟩ := hg.exists_nonneg_const
  refine ⟨hg.1, C * 2 ^ d, ?_⟩
  filter_upwards [hle, (tendsto_add_atTop_nat a).eventually hC, eventually_ge_atTop a]
    with i hi hCi hia
  refine (Nat.cast_le.mpr hi).trans (hCi.trans ?_)
  have hstep : ((i + a : ℕ) : ℝ) ^ d ≤ 2 ^ d * (i : ℝ) ^ d := by
    have h2 : ((i + a : ℕ) : ℝ) ≤ 2 * (i : ℝ) := by
      push_cast
      have : (a : ℝ) ≤ (i : ℝ) := by exact_mod_cast hia
      linarith
    calc ((i + a : ℕ) : ℝ) ^ d ≤ (2 * (i : ℝ)) ^ d :=
          Real.rpow_le_rpow (by positivity) h2 hg.1
      _ = 2 ^ d * (i : ℝ) ^ d := Real.mul_rpow (by norm_num) (Nat.cast_nonneg i)
  calc C * ((i + a : ℕ) : ℝ) ^ d ≤ C * (2 ^ d * (i : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left hstep hC0
    _ = C * 2 ^ d * (i : ℝ) ^ d := by ring

/-- Domination after a backward shift of the argument transfers growth exponents:
if `h i ≤ g (i - a)` eventually, every growth exponent of `g` is one of `h`. -/
theorem IsGrowthExponent.of_le_sub {g h : ℕ → ℕ} {d : ℝ} {a : ℕ}
    (hle : ∀ᶠ i : ℕ in atTop, h i ≤ g (i - a)) (hg : IsGrowthExponent g d) :
    IsGrowthExponent h d := by
  obtain ⟨C, hC0, hC⟩ := hg.exists_nonneg_const
  refine ⟨hg.1, C, ?_⟩
  filter_upwards [hle, (tendsto_sub_atTop_nat a).eventually hC] with i hi hCi
  refine (Nat.cast_le.mpr hi).trans (hCi.trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ hC0
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le i a) hg.1

/-! ### Shift invariance and the squeeze lemma -/

/-- Shifting the argument by a constant does not change the growth exponents.
No monotonicity of `h` is needed. -/
theorem growthExponents_shift (h : ℕ → ℕ) (k : ℕ) :
    growthExponents (fun i => h (i + k)) = growthExponents h := by
  ext d
  constructor
  · intro hd
    exact IsGrowthExponent.of_le_sub (g := fun i => h (i + k)) (a := k)
      (by filter_upwards [eventually_ge_atTop k] with i hi
          simp [Nat.sub_add_cancel hi]) hd
  · intro hd
    exact IsGrowthExponent.of_le_add (g := h) (a := k)
      (Eventually.of_forall fun i => le_rfl) hd

/-- Two sequences that dominate each other after bounded forward shifts of the
argument have the same growth exponents.  This is the load-bearing lemma: it is
what makes a growth degree independent of a choice of comparable filtration. -/
theorem growthExponents_eq_of_shift_squeeze {g h : ℕ → ℕ} {a b : ℕ}
    (hgh : ∀ᶠ i : ℕ in atTop, g i ≤ h (i + a)) (hhg : ∀ᶠ i : ℕ in atTop, h i ≤ g (i + b)) :
    growthExponents g = growthExponents h := by
  ext d
  exact ⟨fun hd => IsGrowthExponent.of_le_add hhg hd,
    fun hd => IsGrowthExponent.of_le_add hgh hd⟩

/-! ## The growth degree -/

/-- The growth degree of `h`: the infimum in `EReal` of its growth exponents.
It is `⊤` exactly when `h` has superpolynomial growth, and otherwise a real
number in `[0, ∞)`. -/
noncomputable def growthDegree (h : ℕ → ℕ) : EReal :=
  sInf ((fun d : ℝ => (d : EReal)) '' growthExponents h)

theorem growthDegree_le {h : ℕ → ℕ} {d : ℝ} (hd : IsGrowthExponent h d) :
    growthDegree h ≤ (d : EReal) :=
  sInf_le ⟨d, hd, rfl⟩

theorem le_growthDegree {h : ℕ → ℕ} {x : EReal}
    (hx : ∀ d : ℝ, IsGrowthExponent h d → x ≤ (d : EReal)) : x ≤ growthDegree h := by
  refine le_sInf ?_
  rintro _ ⟨d, hd, rfl⟩
  exact hx d hd

theorem growthDegree_nonneg (h : ℕ → ℕ) : 0 ≤ growthDegree h :=
  le_growthDegree fun _ hd => by exact_mod_cast hd.1

/-- `growthDegree h = ⊤` exactly when `h` has no growth exponent at all. -/
theorem growthDegree_eq_top_iff (h : ℕ → ℕ) :
    growthDegree h = ⊤ ↔ growthExponents h = ∅ := by
  constructor
  · intro htop
    by_contra hne
    obtain ⟨d, hd⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have := growthDegree_le hd
    rw [htop] at this
    exact (EReal.coe_lt_top d).not_ge this
  · intro hempty
    rw [growthDegree, hempty, Set.image_empty, sInf_empty]

/-- A smaller set of growth exponents means a larger growth degree. -/
theorem growthDegree_mono {g h : ℕ → ℕ} (hsub : growthExponents g ⊆ growthExponents h) :
    growthDegree h ≤ growthDegree g :=
  sInf_le_sInf (Set.image_mono hsub)

theorem growthDegree_congr {g h : ℕ → ℕ} (heq : growthExponents g = growthExponents h) :
    growthDegree g = growthDegree h := by
  rw [growthDegree, growthDegree, heq]

/-- The growth degree is invariant under shifting the filtration index by a
constant. -/
theorem growthDegree_shift (h : ℕ → ℕ) (k : ℕ) :
    growthDegree (fun i => h (i + k)) = growthDegree h :=
  growthDegree_congr (growthExponents_shift h k)

/-- The growth degree is invariant under mutual domination up to bounded shifts.
This is the form used to show that a dimension read off a filtration does not
depend on the chosen filtration. -/
theorem growthDegree_eq_of_shift_squeeze {g h : ℕ → ℕ} {a b : ℕ}
    (hgh : ∀ᶠ i : ℕ in atTop, g i ≤ h (i + a)) (hhg : ∀ᶠ i : ℕ in atTop, h i ≤ g (i + b)) :
    growthDegree g = growthDegree h :=
  growthDegree_congr (growthExponents_eq_of_shift_squeeze hgh hhg)

/-! ## Two-sided power bounds determine the growth degree -/

/-- A lower bound `c * i ^ n ≤ h i` with `c > 0` forbids every exponent below
`n`. -/
theorem not_isGrowthExponent_of_lt {h : ℕ → ℕ} {n c : ℝ} (hc : 0 < c)
    (hlb : ∀ᶠ i : ℕ in atTop, c * (i : ℝ) ^ n ≤ (h i : ℝ)) {d : ℝ} (hdn : d < n) :
    ¬ IsGrowthExponent h d := by
  intro hd
  obtain ⟨C, hC0, hC⟩ := hd.exists_nonneg_const
  have hkey : ∀ᶠ i : ℕ in atTop, c * (i : ℝ) ^ (n - d) ≤ C := by
    filter_upwards [hlb, hC, eventually_ge_atTop 1] with i hi hCi hi1
    have hipos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hi1
    have hsplit : (i : ℝ) ^ n = (i : ℝ) ^ (n - d) * (i : ℝ) ^ d := by
      rw [← Real.rpow_add hipos]; ring_nf
    have hpow : (0 : ℝ) < (i : ℝ) ^ d := Real.rpow_pos_of_pos hipos d
    have hmul : c * (i : ℝ) ^ (n - d) * (i : ℝ) ^ d ≤ C * (i : ℝ) ^ d := by
      calc c * (i : ℝ) ^ (n - d) * (i : ℝ) ^ d = c * (i : ℝ) ^ n := by rw [hsplit]; ring
        _ ≤ (h i : ℝ) := hi
        _ ≤ C * (i : ℝ) ^ d := hCi
    exact le_of_mul_le_mul_right hmul hpow
  have htend : Tendsto (fun i : ℕ => c * (i : ℝ) ^ (n - d)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc
      ((tendsto_rpow_atTop (sub_pos.mpr hdn)).comp tendsto_natCast_atTop_atTop)
  obtain ⟨i, hi1, hi2⟩ := ((htend.eventually_gt_atTop C).and hkey).exists
  exact absurd hi2 (not_le.mpr hi1)

/-- Matching upper and lower power bounds pin the growth exponents to
`Set.Ici n`. -/
theorem growthExponents_eq_Ici {h : ℕ → ℕ} {n : ℝ} (hub : IsGrowthExponent h n)
    {c : ℝ} (hc : 0 < c) (hlb : ∀ᶠ i : ℕ in atTop, c * (i : ℝ) ^ n ≤ (h i : ℝ)) :
    growthExponents h = Set.Ici n := by
  ext d
  refine ⟨fun hd => Set.mem_Ici.mpr ?_, fun hd => hub.mono (Set.mem_Ici.mp hd)⟩
  by_contra hlt
  exact not_isGrowthExponent_of_lt hc hlb (not_le.mp hlt) hd

private theorem sInf_image_Ici (n : ℝ) :
    sInf ((fun d : ℝ => (d : EReal)) '' Set.Ici n) = (n : EReal) := by
  refine le_antisymm (sInf_le ⟨n, Set.mem_Ici.mpr le_rfl, rfl⟩) (le_sInf ?_)
  rintro _ ⟨d, hd, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (Set.mem_Ici.mp hd)

/-- Matching upper and lower power bounds determine the growth degree. -/
theorem growthDegree_eq_of_bounds {h : ℕ → ℕ} {n : ℝ} (hub : IsGrowthExponent h n)
    {c : ℝ} (hc : 0 < c) (hlb : ∀ᶠ i : ℕ in atTop, c * (i : ℝ) ^ n ≤ (h i : ℝ)) :
    growthDegree h = (n : EReal) := by
  rw [growthDegree, growthExponents_eq_Ici hub hc hlb, sInf_image_Ici]

/-! ## Eventually polynomial Hilbert functions -/

open Polynomial in
/-- A polynomial with positive leading coefficient is eventually squeezed between
two positive multiples of `x ^ natDegree`. -/
theorem eventually_bounds_of_leadingCoeff_pos {p : ℝ[X]} (hlead : 0 < p.leadingCoeff) :
    ∀ᶠ x : ℝ in atTop, p.leadingCoeff / 2 * x ^ p.natDegree ≤ p.eval x ∧
      p.eval x ≤ 3 * p.leadingCoeff / 2 * x ^ p.natDegree := by
  have hb := p.isEquivalent_atTop_lead.isLittleO.def (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hxn : (0 : ℝ) ≤ x ^ p.natDegree := pow_nonneg hx0 _
  have hnorm : ‖p.leadingCoeff * x ^ p.natDegree‖ = p.leadingCoeff * x ^ p.natDegree := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Pi.sub_apply, Real.norm_eq_abs, hnorm] at hx
  have habs := abs_le.mp hx
  constructor <;> nlinarith [habs.1, habs.2]

open Polynomial in
/-- A polynomial whose values on large naturals are those of a `ℕ`-valued
function, and which is not the zero polynomial, has positive leading
coefficient. -/
theorem leadingCoeff_pos_of_eventually_eq {h : ℕ → ℕ} {p : ℝ[X]} (hp : p ≠ 0)
    (heq : ∀ᶠ i : ℕ in atTop, (h i : ℝ) = p.eval (i : ℝ)) : 0 < p.leadingCoeff := by
  rcases lt_trichotomy p.leadingCoeff 0 with hlt | hz | hpos
  · exfalso
    have hb := p.isEquivalent_atTop_lead.isLittleO.def (show (0 : ℝ) < 1 / 2 by norm_num)
    have hR : ∀ᶠ x : ℝ in atTop, p.eval x < 0 := by
      filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hx hx1
      have hxn : (0 : ℝ) < x ^ p.natDegree := pow_pos (lt_of_lt_of_le zero_lt_one hx1) _
      have hnorm : ‖p.leadingCoeff * x ^ p.natDegree‖ = -p.leadingCoeff * x ^ p.natDegree := by
        rw [Real.norm_eq_abs, abs_of_nonpos (by nlinarith)]; ring
      rw [Pi.sub_apply, Real.norm_eq_abs, hnorm] at hx
      have habs := abs_le.mp hx
      nlinarith [habs.2]
    obtain ⟨i, hi1, hi2⟩ :=
      (heq.and ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually hR)).exists
    have hnn : (0 : ℝ) ≤ (h i : ℝ) := Nat.cast_nonneg _
    rw [hi1] at hnn
    exact absurd hi2 (not_lt.mpr hnn)
  · exact absurd hz (leadingCoeff_ne_zero.mpr hp)
  · exact hpos

open Polynomial in
/-- If `h` eventually agrees with the values of a polynomial with positive
leading coefficient, its growth degree is the degree of that polynomial. -/
theorem growthDegree_eq_natDegree_of_leadingCoeff_pos {h : ℕ → ℕ} {p : ℝ[X]}
    (hlead : 0 < p.leadingCoeff)
    (heq : ∀ᶠ i : ℕ in atTop, (h i : ℝ) = p.eval (i : ℝ)) :
    growthDegree h = ((p.natDegree : ℝ) : EReal) := by
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually
    (eventually_bounds_of_leadingCoeff_pos hlead)
  have hrp : ∀ i : ℕ, (i : ℝ) ^ ((p.natDegree : ℕ) : ℝ) = (i : ℝ) ^ p.natDegree :=
    fun i => Real.rpow_natCast _ _
  have hub : IsGrowthExponent h ((p.natDegree : ℕ) : ℝ) := by
    refine ⟨Nat.cast_nonneg _, 3 * p.leadingCoeff / 2, ?_⟩
    filter_upwards [heq, hnat] with i hi hbnd
    rw [hi, hrp i]
    exact hbnd.2
  refine growthDegree_eq_of_bounds hub (c := p.leadingCoeff / 2) (by linarith) ?_
  filter_upwards [heq, hnat] with i hi hbnd
  rw [hi, hrp i]
  exact hbnd.1

open Polynomial in
/-- **Eventually polynomial Hilbert functions.**  If `h` is eventually equal to
the values of a polynomial, its growth degree is the degree of that polynomial.

No hypothesis on `p` is needed.  For `p ≠ 0` the positivity of the leading
coefficient is forced by the fact that `h` takes values in `ℕ`
(`leadingCoeff_pos_of_eventually_eq`); for `p = 0` the function `h` is
eventually `0`, every nonnegative exponent works, and both sides are `0`. -/
theorem growthDegree_eq_natDegree_of_eventually_eq {h : ℕ → ℕ} {p : ℝ[X]}
    (heq : ∀ᶠ i : ℕ in atTop, (h i : ℝ) = p.eval (i : ℝ)) :
    growthDegree h = ((p.natDegree : ℝ) : EReal) := by
  rcases eq_or_ne p 0 with rfl | hp
  · have hz : ∀ᶠ i : ℕ in atTop, (h i : ℝ) = 0 := by simpa using heq
    have hset : growthExponents h = Set.Ici 0 := by
      ext d
      refine ⟨fun hd => Set.mem_Ici.mpr hd.1, fun hd => ⟨Set.mem_Ici.mp hd, 0, ?_⟩⟩
      filter_upwards [hz] with i hi
      simp [hi]
    rw [growthDegree, hset, sInf_image_Ici]
    simp
  · exact growthDegree_eq_natDegree_of_leadingCoeff_pos
      (leadingCoeff_pos_of_eventually_eq hp heq) heq

/-! ## Application to Hilbert functions of comparable filtrations -/

section Comparison

variable {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]

/-- If each piece of `G` sits inside a bounded shift of `G'` and conversely, the
Hilbert functions of `G` and `G'` have the same growth degree.

This is the invariance statement the rest of a filtered-dimension theory needs.
The comparison hypotheses are stated directly and are not derived here from any
notion of good filtration. -/
theorem growthDegree_hilbertFunction_eq_of_bounded_shift {G G' : ℕ → Submodule K M} {a b : ℕ}
    (hfin : ∀ i, Module.Finite K (G i)) (hfin' : ∀ i, Module.Finite K (G' i))
    (hGG' : ∀ i, G i ≤ G' (i + a)) (hG'G : ∀ i, G' i ≤ G (i + b)) :
    growthDegree (hilbertFunction G) = growthDegree (hilbertFunction G') := by
  refine growthDegree_eq_of_shift_squeeze (a := a) (b := b)
    (Eventually.of_forall fun i => ?_) (Eventually.of_forall fun i => ?_)
  · have := hfin' (i + a)
    exact Submodule.finrank_mono (hGG' i)
  · have := hfin (i + b)
    exact Submodule.finrank_mono (hG'G i)

end Comparison

end HilbertFunction
end AlgebraicAnalysis
