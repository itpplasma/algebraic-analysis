-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Gelfand-Kirillov dimension of a filtered module

Let `K` be a field and `M` a `K`-module equipped with a filtration `F : ℕ → Submodule K M` whose
pieces are finite dimensional.  Its *Hilbert function* is `n ↦ finrank K (F n)`, and its
*Gelfand-Kirillov dimension* is the polynomial growth degree of that function:

`gkDim F = sInf {d : ℝ≥0 | ∃ C, ∀ n, finrank K (F n) ≤ C * (n + 1) ^ d}`,

computed in `ℝ≥0∞` so that a filtration of faster than polynomial growth receives the value `⊤`.

## What is proved here

* `gkDim_eq_of_shiftEquivalent`: the invariant only depends on the filtration up to a bounded
  shift in the index, `ShiftEquivalent`.  Bounded shift equivalence is the only comparison
  hypothesis used; no notion of good filtration is assumed anywhere in this file.
* `gkDim_subFiltration_le`, `gkDim_quotient_le` and `gkDim_eq_sup`: for the filtrations induced
  on a submodule and on the corresponding quotient the Hilbert functions add exactly
  (`hilbertFunction_sub_add_quot`), so each end of the short exact sequence has dimension at most
  that of the middle term, and the middle term has exactly the maximum of the two.  Transporting
  the last statement to filtrations that are not the induced ones is done through
  `gkDim_eq_sup_of_shiftEquivalent`, whose shift-equivalence hypotheses are explicit; that is
  where a goodness assumption would be used downstream.
* `gkDim_eq_zero_of_finite`: a finite dimensional module has dimension `0` for every filtration.
  Note that the `ℝ≥0∞`-valued convention used here also assigns `0` to the zero module, where
  some authors prefer `-∞`; the statement is therefore not restricted to nonzero modules.
* `gkDim_totalDegreeFiltration`: the polynomial ring in `n` variables, filtered by total degree,
  has dimension exactly `n`.  Its Hilbert function is computed exactly in
  `finrank_restrictTotalDegree`: `finrank K (restrictTotalDegree (Fin n) K m) = (m + n).choose n`.

## What is not proved here

`BernsteinInequality` is *stated* and deliberately left unproved; it is the open target of this
layer.  It is a `Prop`-valued definition, not a hypothesis of any theorem in this file, and
nothing below depends on it.

## Implementation notes

Growth is measured against `(n + 1) ^ d` rather than `n ^ d` so that the bound at `n = 0` carries
no information; the two conventions give the same infimum.  Real exponents are used, so `gkDim`
is not forced to be an integer, matching the general definition.
-/

namespace AlgebraicAnalysis
namespace GKDimension

open scoped ENNReal NNReal
open Nat

universe u v w

/-! ## Polynomial growth degree of a numeric function -/

/-- `d` is a polynomial growth exponent of `H` when `H n ≤ C * (n + 1) ^ d` holds for some
constant `C` and all `n`.  The exponent is a nonnegative real, not necessarily an integer. -/
def growthExponents (H : ℕ → ℕ) : Set ℝ≥0 :=
  {d | ∃ C : ℝ≥0, ∀ n : ℕ, (H n : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ (d : ℝ)}

/-- The polynomial growth degree of a numeric function: the infimum of its growth exponents,
taken in `ℝ≥0∞`, so that a function with no polynomial bound has growth degree `⊤`. -/
noncomputable def growthDegree (H : ℕ → ℕ) : ℝ≥0∞ :=
  sInf ((↑) '' growthExponents H)

variable {H H₁ H₂ : ℕ → ℕ} {d e : ℝ≥0}

private theorem one_le_cast_add_one (n : ℕ) : (1 : ℝ) ≤ (n : ℝ) + 1 := by
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem growthDegree_le_coe (hd : d ∈ growthExponents H) : growthDegree H ≤ (d : ℝ≥0∞) :=
  sInf_le ⟨d, hd, rfl⟩

theorem le_growthDegree (h : ∀ e ∈ growthExponents H, d ≤ e) :
    (d : ℝ≥0∞) ≤ growthDegree H := by
  refine le_sInf ?_
  rintro _ ⟨e, he, rfl⟩
  exact_mod_cast h e he

/-- The set of growth exponents is upward closed. -/
theorem growthExponents_upward (hd : d ∈ growthExponents H) (hde : d ≤ e) :
    e ∈ growthExponents H := by
  obtain ⟨C, hC⟩ := hd
  refine ⟨C, fun n => (hC n).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ C.coe_nonneg
  exact Real.rpow_le_rpow_of_exponent_le (one_le_cast_add_one n) (by exact_mod_cast hde)

/-- A pointwise smaller function has smaller growth degree. -/
theorem growthDegree_mono (h : ∀ n, H₁ n ≤ H₂ n) : growthDegree H₁ ≤ growthDegree H₂ := by
  refine sInf_le_sInf ?_
  rintro _ ⟨d, ⟨C, hC⟩, rfl⟩
  exact ⟨d, ⟨C, fun n => le_trans (by exact_mod_cast h n) (hC n)⟩, rfl⟩

/-- Comparison up to a bounded shift of the index does not change the growth degree. -/
theorem growthDegree_le_of_le_shift (c : ℕ) (h : ∀ n, H₁ n ≤ H₂ (n + c)) :
    growthDegree H₁ ≤ growthDegree H₂ := by
  refine sInf_le_sInf ?_
  rintro _ ⟨d, ⟨C, hC⟩, rfl⟩
  refine ⟨d, ⟨C * ((c : ℝ≥0) + 1) ^ (d : ℝ), fun n => ?_⟩, rfl⟩
  have hbase : ((n : ℝ) + (c : ℝ)) + 1 ≤ ((c : ℝ) + 1) * ((n : ℝ) + 1) := by
    nlinarith [n.cast_nonneg (α := ℝ), c.cast_nonneg (α := ℝ)]
  have hstep : (((n : ℝ) + (c : ℝ)) + 1) ^ (d : ℝ)
      ≤ ((c : ℝ) + 1) ^ (d : ℝ) * ((n : ℝ) + 1) ^ (d : ℝ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hbase d.coe_nonneg
  calc (H₁ n : ℝ) ≤ (H₂ (n + c) : ℝ) := by exact_mod_cast h n
    _ ≤ (C : ℝ) * (((n + c : ℕ) : ℝ) + 1) ^ (d : ℝ) := hC (n + c)
    _ = (C : ℝ) * (((n : ℝ) + (c : ℝ)) + 1) ^ (d : ℝ) := by push_cast; ring_nf
    _ ≤ (C : ℝ) * (((c : ℝ) + 1) ^ (d : ℝ) * ((n : ℝ) + 1) ^ (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep C.coe_nonneg
    _ = ((C * ((c : ℝ≥0) + 1) ^ (d : ℝ) : ℝ≥0) : ℝ) * ((n : ℝ) + 1) ^ (d : ℝ) := by
        push_cast [NNReal.coe_rpow]; ring

/-- The maximum of two growth exponents is a growth exponent of the pointwise sum. -/
theorem growthExponents_sup_mem {d₁ d₂ : ℝ≥0} (h₁ : d₁ ∈ growthExponents H₁)
    (h₂ : d₂ ∈ growthExponents H₂) :
    d₁ ⊔ d₂ ∈ growthExponents (fun n => H₁ n + H₂ n) := by
  obtain ⟨C₁, hC₁⟩ := growthExponents_upward h₁ (le_sup_left (b := d₂))
  obtain ⟨C₂, hC₂⟩ := growthExponents_upward h₂ (le_sup_right (a := d₁))
  refine ⟨C₁ + C₂, fun n => ?_⟩
  have := add_le_add (hC₁ n) (hC₂ n)
  push_cast
  push_cast at this
  linarith

/-- The growth degree of a pointwise sum is at most the maximum of the two growth degrees. -/
theorem growthDegree_add_le :
    growthDegree (fun n => H₁ n + H₂ n) ≤ growthDegree H₁ ⊔ growthDegree H₂ := by
  by_contra hcon
  rw [not_le] at hcon
  have h1 : growthDegree H₁ < growthDegree (fun n => H₁ n + H₂ n) :=
    lt_of_le_of_lt le_sup_left hcon
  have h2 : growthDegree H₂ < growthDegree (fun n => H₁ n + H₂ n) :=
    lt_of_le_of_lt le_sup_right hcon
  obtain ⟨_, ⟨d₁, hd₁, rfl⟩, hlt1⟩ := sInf_lt_iff.mp h1
  obtain ⟨_, ⟨d₂, hd₂, rfl⟩, hlt2⟩ := sInf_lt_iff.mp h2
  have hle : growthDegree (fun n => H₁ n + H₂ n) ≤ ((d₁ ⊔ d₂ : ℝ≥0) : ℝ≥0∞) :=
    growthDegree_le_coe (growthExponents_sup_mem hd₁ hd₂)
  have hmax : ((d₁ ⊔ d₂ : ℝ≥0) : ℝ≥0∞) < growthDegree (fun n => H₁ n + H₂ n) := by
    rw [ENNReal.coe_max]
    exact max_lt hlt1 hlt2
  exact absurd hle (not_le.mpr hmax)

/-- A bounded function has growth degree `0`. -/
theorem growthDegree_eq_zero_of_bounded {B : ℕ} (h : ∀ n, H n ≤ B) : growthDegree H = 0 := by
  refine le_antisymm ?_ _root_.zero_le
  have : (0 : ℝ≥0) ∈ growthExponents H := by
    refine ⟨(B : ℝ≥0), fun n => ?_⟩
    simp only [NNReal.coe_zero, Real.rpow_zero, mul_one, NNReal.coe_natCast]
    exact_mod_cast h n
  simpa using growthDegree_le_coe this

/-- A lower bound `c * (n + 1) ^ e ≤ H n` with `c > 0` forces the growth degree to be at
least `e`. -/
theorem le_growthDegree_of_pow_le {c : ℝ} (hc : 0 < c)
    (h : ∀ n : ℕ, c * ((n : ℝ) + 1) ^ (e : ℝ) ≤ (H n : ℝ)) :
    (e : ℝ≥0∞) ≤ growthDegree H := by
  refine le_growthDegree ?_
  intro d hd
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨C, hC⟩ := hd
  have hdlt : (d : ℝ) < (e : ℝ) := by exact_mod_cast hlt
  set ε : ℝ := (e : ℝ) - (d : ℝ) with hε
  have hεpos : 0 < ε := by rw [hε]; exact sub_pos.mpr hdlt
  -- after dividing by `(n + 1) ^ d`, the lower bound gives a uniform bound on `(n + 1) ^ ε`
  have hbound : ∀ n : ℕ, c * ((n : ℝ) + 1) ^ ε ≤ (C : ℝ) := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ (d : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    have hsplit : ((n : ℝ) + 1) ^ (e : ℝ)
        = ((n : ℝ) + 1) ^ (d : ℝ) * ((n : ℝ) + 1) ^ ε := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      simp [hε]
    have h1 : c * (((n : ℝ) + 1) ^ (d : ℝ) * ((n : ℝ) + 1) ^ ε)
        ≤ (C : ℝ) * ((n : ℝ) + 1) ^ (d : ℝ) := by
      calc c * (((n : ℝ) + 1) ^ (d : ℝ) * ((n : ℝ) + 1) ^ ε)
          = c * ((n : ℝ) + 1) ^ (e : ℝ) := by rw [hsplit]
        _ ≤ (H n : ℝ) := h n
        _ ≤ (C : ℝ) * ((n : ℝ) + 1) ^ (d : ℝ) := hC n
    nlinarith [hpos]
  -- but `(n + 1) ^ ε` is unbounded
  set B : ℝ := ((C : ℝ) / c + 1) ^ (1 / ε) with hB
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have hBnonneg : (0 : ℝ) ≤ (C : ℝ) / c + 1 := by positivity
  have hgrow : (C : ℝ) / c + 1 < ((n : ℝ) + 1) ^ ε := by
    have hlt' : B < (n : ℝ) + 1 := by linarith
    have hBn : (0 : ℝ) ≤ B := by
      rw [hB]; exact Real.rpow_nonneg hBnonneg _
    have := Real.rpow_lt_rpow hBn hlt' hεpos
    rwa [hB, ← Real.rpow_mul hBnonneg, one_div, inv_mul_cancel₀ hεpos.ne', Real.rpow_one] at this
  have h1 : c * ((C : ℝ) / c + 1) < c * (((n : ℝ) + 1) ^ ε) := by
    exact mul_lt_mul_of_pos_left hgrow hc
  have h2 : c * ((C : ℝ) / c + 1) = (C : ℝ) + c := by field_simp
  linarith [hbound n]

/-! ## Hilbert function and Gelfand-Kirillov dimension of a filtered module -/

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The Hilbert function of a filtration of a `K`-module: the dimension of each filtration
piece.  It carries information only when the pieces are finite dimensional; `Module.finrank`
returns `0` otherwise, so every statement below assumes finiteness explicitly. -/
noncomputable def hilbertFunction (F : ℕ → Submodule K M) (n : ℕ) : ℕ :=
  Module.finrank K (F n)

/-- The Gelfand-Kirillov dimension of a filtered module: the polynomial growth degree of its
Hilbert function.  No goodness, exhaustiveness or module-structure hypothesis on the filtration
enters the definition. -/
noncomputable def gkDim (F : ℕ → Submodule K M) : ℝ≥0∞ :=
  growthDegree (hilbertFunction F)

/-! ### Independence of the filtration up to bounded shift -/

/-- Two filtrations of the same module are *shift equivalent* when each is contained in a
bounded shift of the other.  This is the equivalence relation under which the
Gelfand-Kirillov dimension is invariant; for filtrations arising from two finite generating
sets of a module over a filtered ring it is the conclusion of the usual comparison argument,
which is not carried out here. -/
def ShiftEquivalent (F G : ℕ → Submodule K M) : Prop :=
  ∃ c : ℕ, (∀ n, F n ≤ G (n + c)) ∧ ∀ n, G n ≤ F (n + c)

theorem shiftEquivalent_comm {F G : ℕ → Submodule K M} (h : ShiftEquivalent F G) :
    ShiftEquivalent G F := by
  obtain ⟨c, h₁, h₂⟩ := h
  exact ⟨c, h₂, h₁⟩

/-- **Independence of the filtration.**  Shift equivalent filtrations by finite dimensional
subspaces have the same Gelfand-Kirillov dimension. -/
theorem gkDim_eq_of_shiftEquivalent {F G : ℕ → Submodule K M}
    (hF : ∀ n, Module.Finite K (F n)) (hG : ∀ n, Module.Finite K (G n))
    (h : ShiftEquivalent F G) : gkDim F = gkDim G := by
  obtain ⟨c, hFG, hGF⟩ := h
  refine le_antisymm (growthDegree_le_of_le_shift c fun n => ?_)
    (growthDegree_le_of_le_shift c fun n => ?_)
  · have := hG (n + c)
    exact Submodule.finrank_mono (hFG n)
  · have := hF (n + c)
    exact Submodule.finrank_mono (hGF n)

/-! ### Behaviour in short exact sequences -/

variable (N : Submodule K M)

/-- The filtration induced on a submodule. -/
def subFiltration (F : ℕ → Submodule K M) : ℕ → Submodule K N :=
  fun n => (F n).comap N.subtype

/-- The filtration induced on a quotient module. -/
def quotFiltration (F : ℕ → Submodule K M) : ℕ → Submodule K (M ⧸ N) :=
  fun n => (F n).map N.mkQ

variable {N}

private theorem finrank_comap_subtype (p q : Submodule K M) :
    Module.finrank K (Submodule.comap p.subtype q) = Module.finrank K (p ⊓ q : Submodule K M) := by
  have e : (Submodule.comap p.subtype q) ≃ₗ[K]
      ((Submodule.comap p.subtype q).map p.subtype) :=
    Submodule.equivMapOfInjective _ (Submodule.injective_subtype p) _
  rw [e.finrank_eq, Submodule.map_comap_subtype]

/-- **Additivity of the Hilbert function.**  For the induced filtrations the dimensions of the
sub- and quotient pieces add up to the dimension of the ambient piece. -/
theorem hilbertFunction_sub_add_quot (F : ℕ → Submodule K M)
    (hF : ∀ n, Module.Finite K (F n)) (n : ℕ) :
    hilbertFunction (subFiltration N F) n + hilbertFunction (quotFiltration N F) n
      = hilbertFunction F n := by
  have := hF n
  set f : (F n) →ₗ[K] M ⧸ N := N.mkQ.comp (F n).subtype with hf
  have hker : LinearMap.ker f = Submodule.comap (F n).subtype N := by
    rw [hf, LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range f = (F n).map N.mkQ := by
    rw [hf, LinearMap.range_comp, Submodule.range_subtype]
  have hrn := f.finrank_range_add_finrank_ker
  rw [hker, hrange, finrank_comap_subtype] at hrn
  have hsub : hilbertFunction (subFiltration N F) n
      = Module.finrank K (F n ⊓ N : Submodule K M) := by
    rw [hilbertFunction, subFiltration, finrank_comap_subtype, inf_comm]
  rw [hsub, hilbertFunction, hilbertFunction, quotFiltration]
  omega

/-- A submodule has Gelfand-Kirillov dimension at most that of the ambient module. -/
theorem gkDim_subFiltration_le (F : ℕ → Submodule K M) (hF : ∀ n, Module.Finite K (F n)) :
    gkDim (subFiltration N F) ≤ gkDim F :=
  growthDegree_mono fun n => by
    have := hilbertFunction_sub_add_quot (N := N) F hF n; omega

/-- A quotient module has Gelfand-Kirillov dimension at most that of the ambient module. -/
theorem gkDim_quotFiltration_le (F : ℕ → Submodule K M) (hF : ∀ n, Module.Finite K (F n)) :
    gkDim (quotFiltration N F) ≤ gkDim F :=
  growthDegree_mono fun n => by
    have := hilbertFunction_sub_add_quot (N := N) F hF n; omega

/-- **Short exact sequences.**  For the induced filtrations, the Gelfand-Kirillov dimension of
the middle term is the maximum of the dimensions of the two ends. -/
theorem gkDim_eq_sup (F : ℕ → Submodule K M) (hF : ∀ n, Module.Finite K (F n)) :
    gkDim F = gkDim (subFiltration N F) ⊔ gkDim (quotFiltration N F) := by
  refine le_antisymm ?_ (sup_le (gkDim_subFiltration_le F hF) (gkDim_quotFiltration_le F hF))
  have hfun : hilbertFunction F = fun n =>
      hilbertFunction (subFiltration N F) n + hilbertFunction (quotFiltration N F) n := by
    funext n
    exact (hilbertFunction_sub_add_quot (N := N) F hF n).symm
  rw [gkDim, hfun]
  exact growthDegree_add_le

/-- The maximum statement for filtrations of the sub- and quotient module that are not the
induced ones.  The comparison hypotheses are bounded shift equivalences with the induced
filtrations; downstream they are supplied by a goodness assumption, which is not formalized
here. -/
theorem gkDim_eq_sup_of_shiftEquivalent (F : ℕ → Submodule K M)
    (hF : ∀ n, Module.Finite K (F n))
    (G : ℕ → Submodule K N) (G' : ℕ → Submodule K (M ⧸ N))
    (hGfin : ∀ n, Module.Finite K (G n)) (hG'fin : ∀ n, Module.Finite K (G' n))
    (hsubfin : ∀ n, Module.Finite K (subFiltration N F n))
    (hquotfin : ∀ n, Module.Finite K (quotFiltration N F n))
    (hG : ShiftEquivalent G (subFiltration N F))
    (hG' : ShiftEquivalent G' (quotFiltration N F)) :
    gkDim F = gkDim G ⊔ gkDim G' := by
  rw [gkDim_eq_of_shiftEquivalent hGfin hsubfin hG,
    gkDim_eq_of_shiftEquivalent hG'fin hquotfin hG']
  exact gkDim_eq_sup F hF

/-! ### Base case: finite dimensional modules -/

/-- A finite dimensional module has Gelfand-Kirillov dimension `0` for every filtration.  The
`ℝ≥0∞`-valued convention used here assigns `0` to the zero module as well; for a nonzero
finite dimensional module this is the expected value. -/
theorem gkDim_eq_zero_of_finite [Module.Finite K M] (F : ℕ → Submodule K M) : gkDim F = 0 :=
  growthDegree_eq_zero_of_bounded (B := Module.finrank K M) fun _ => Submodule.finrank_le _

/-! ## The polynomial ring with its total degree filtration -/

section Polynomial

/-- Hockey stick summation in the form needed for the Hilbert function of the polynomial
ring. -/
private theorem sum_add_choose (p : ℕ) : ∀ m : ℕ,
    ∑ k ∈ Finset.range (m + 1), (p + k).choose p = (m + p + 1).choose (p + 1)
  | 0 => by simp
  | (m + 1) => by
      rw [Finset.sum_range_succ, sum_add_choose p m,
        show m + 1 + p + 1 = (m + p + 1) + 1 by ring,
        show p + (m + 1) = m + p + 1 by ring, Nat.choose_succ_succ (m + p + 1) p]
      ring

/-- The number of monomials in `n` variables of total degree at most `m` is `(m + n).choose n`. -/
theorem card_finsupp_sum_le (n m : ℕ) :
    Nat.card {s : Fin n →₀ ℕ | (s.sum fun _ e => e) ≤ m} = (m + n).choose n := by
  classical
  set T : Finset (Fin n →₀ ℕ) :=
    (Finset.range (m + 1)).biUnion
      (fun k => (Finset.univ : Finset (Fin n)).finsuppAntidiag k) with hT
  have hset : {s : Fin n →₀ ℕ | (s.sum fun _ e => e) ≤ m} = (↑T : Set (Fin n →₀ ℕ)) := by
    ext s
    simp only [hT, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_range,
      Finset.mem_finsuppAntidiag', Set.mem_ofPred_eq, Finset.subset_univ, and_true,
      exists_prop]
    constructor
    · intro h
      exact ⟨_, Nat.lt_succ_of_le h, rfl⟩
    · rintro ⟨k, hk, hsum⟩
      omega
  have hdisj : ∀ x ∈ Finset.range (m + 1), ∀ y ∈ Finset.range (m + 1), x ≠ y →
      Disjoint ((Finset.univ : Finset (Fin n)).finsuppAntidiag x)
        ((Finset.univ : Finset (Fin n)).finsuppAntidiag y) := by
    intro x _ y _ hxy
    refine Finset.disjoint_left.mpr ?_
    intro s hx hy
    rw [Finset.mem_finsuppAntidiag'] at hx hy
    exact hxy (hx.1 ▸ hy.1)
  have hcardT : T.card = ∑ k ∈ Finset.range (m + 1), (n + k - 1).choose k := by
    rw [hT, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun k _ => ?_
    simpa using Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin n))) k
  have hsum : ∑ k ∈ Finset.range (m + 1), (n + k - 1).choose k = (m + n).choose n := by
    cases n with
    | zero =>
        refine (Finset.sum_eq_single_of_mem 0 (by simp) ?_).trans (by simp)
        intro k _ hk
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        simp
    | succ p =>
        have hterm : ∀ k ∈ Finset.range (m + 1),
            (p + 1 + k - 1).choose k = (p + k).choose p := by
          intro k _
          rw [show p + 1 + k - 1 = p + k by omega,
            ← Nat.choose_symm (Nat.le_add_right p k), Nat.add_sub_cancel_left]
        rw [Finset.sum_congr rfl hterm, sum_add_choose p m, Nat.add_assoc]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, hcardT, hsum]

/-- The exact Hilbert function of the polynomial ring in `n` variables filtered by total
degree. -/
theorem finrank_restrictTotalDegree (K : Type*) [Field K] (n m : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K m) = (m + n).choose n := by
  rw [MvPolynomial.restrictTotalDegree,
    Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _)]
  exact card_finsupp_sum_le n m

/-- The total degree filtration of the polynomial ring in `n` variables. -/
noncomputable def totalDegreeFiltration (K : Type*) [Field K] (n : ℕ) :
    ℕ → Submodule K (MvPolynomial (Fin n) K) :=
  fun m => MvPolynomial.restrictTotalDegree (Fin n) K m

theorem hilbertFunction_totalDegreeFiltration (K : Type*) [Field K] (n m : ℕ) :
    hilbertFunction (totalDegreeFiltration K n) m = (m + n).choose n :=
  finrank_restrictTotalDegree K n m

/-- The growth degree of the binomial Hilbert function `m ↦ (m + n).choose n` is exactly `n`. -/
theorem growthDegree_add_choose (n : ℕ) :
    growthDegree (fun m => (m + n).choose n) = (n : ℝ≥0∞) := by
  refine le_antisymm ?_ ?_
  · have hmem : (n : ℝ≥0) ∈ growthExponents (fun m => (m + n).choose n) := by
      refine ⟨1, fun m => ?_⟩
      have h : ((m + n).choose n : ℝ) ≤ (((m + 1) ^ n : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_add_le_add_one_pow m n
      calc ((m + n).choose n : ℝ) ≤ (((m + 1) ^ n : ℕ) : ℝ) := h
        _ = ((m : ℝ) + 1) ^ (n : ℕ) := by push_cast; ring
        _ = ((1 : ℝ≥0) : ℝ) * ((m : ℝ) + 1) ^ (((n : ℝ≥0)) : ℝ) := by
            rw [NNReal.coe_natCast, Real.rpow_natCast]; simp
    simpa using growthDegree_le_coe hmem
  · have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
    refine le_of_eq_of_le (by simp) (le_growthDegree_of_pow_le (e := (n : ℝ≥0))
      (c := 1 / (n ! : ℝ)) (by positivity) fun m => ?_)
    have h := Nat.pow_le_choose (α := ℝ) n (m + n)
    rw [show m + n + 1 - n = m + 1 by omega] at h
    calc 1 / (n ! : ℝ) * ((m : ℝ) + 1) ^ (((n : ℝ≥0)) : ℝ)
        = (((m + 1 : ℕ) : ℝ) ^ n) / (n ! : ℝ) := by
          rw [NNReal.coe_natCast, Real.rpow_natCast]
          push_cast
          ring
      _ ≤ (((m + n).choose n : ℕ) : ℝ) := h

/-- **The polynomial ring in `n` variables has Gelfand-Kirillov dimension exactly `n`** for its
total degree filtration.  This is the computation that pins the normalization of the
definition. -/
theorem gkDim_totalDegreeFiltration (K : Type*) [Field K] (n : ℕ) :
    gkDim (totalDegreeFiltration K n) = (n : ℝ≥0∞) := by
  rw [gkDim, show hilbertFunction (totalDegreeFiltration K n)
      = fun m => (m + n).choose n from funext (hilbertFunction_totalDegreeFiltration K n)]
  exact growthDegree_add_choose n

end Polynomial

/-! ## The Bernstein inequality: statement only -/

/-- **Bernstein inequality**, abstract form.  This is the *open target* of this layer: it is
stated here and is **not** proved, and no theorem in this file uses it.

The hypotheses render, without an associated graded framework, the situation of a filtered
`K`-algebra `A` whose associated graded ring is a polynomial ring in `2 * n` variables, acting
on a nonzero module with a good filtration:

* `hmono`, `hone`, `hmul`, `hexh` make `FA` an exhaustive multiplicative ring filtration;
* `hgr` records that each filtration piece has the dimension of the space of polynomials of
  total degree at most `i` in `2 * n` variables, which is the Hilbert function of the intended
  associated graded ring;
* `hcomm` records that the commutator drops the filtration degree by two;
* `hweyl` records the canonical commutation relations, which is the nondegeneracy of the
  induced Poisson bracket on the associated graded ring;
* on the module side, `F` is an exhaustive filtration by finite dimensional subspaces,
  compatible with `FA`, and eventually generated in each step by `FA 1`, which is the good
  filtration condition for the filtration `FA`.

The last two hypotheses are essential and are the reason the statement is not about
commutative rings: for a commutative `A` the hypothesis `hgr` alone would be satisfied by a
polynomial ring in `2 * n` variables, which has nonzero modules of Gelfand-Kirillov
dimension `0`.  The intended instance of the whole hypothesis package is the `n`-th Weyl
algebra with its Bernstein filtration. -/
def BernsteinInequality (n : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A] (FA : ℕ → Submodule K A),
    Monotone FA →
    (1 : A) ∈ FA 0 →
    (∀ i j, ∀ a ∈ FA i, ∀ b ∈ FA j, a * b ∈ FA (i + j)) →
    (⨆ i, FA i) = ⊤ →
    (∀ i, Module.finrank K (FA i) = (i + 2 * n).choose (2 * n)) →
    (∀ i j, ∀ a ∈ FA i, ∀ b ∈ FA j, a * b - b * a ∈ FA (i + j - 2)) →
    (∃ x p : Fin n → A, (∀ i, x i ∈ FA 1) ∧ (∀ i, p i ∈ FA 1) ∧
      ∀ i j, p i * x j - x j * p i = if i = j then 1 else 0) →
    ∀ (M : Type w) [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
      (F : ℕ → Submodule K M),
    Monotone F →
    (∀ j, Module.Finite K (F j)) →
    (⨆ j, F j) = ⊤ →
    (∀ i j, ∀ a ∈ FA i, ∀ x ∈ F j, a • x ∈ F (i + j)) →
    (∃ j₀ : ℕ, ∀ j ≥ j₀,
      F (j + 1) = Submodule.span K {z : M | ∃ a ∈ FA 1, ∃ y ∈ F j, z = a • y}) →
    Nontrivial M →
    (n : ℝ≥0∞) ≤ gkDim F

end GKDimension
end AlgebraicAnalysis
