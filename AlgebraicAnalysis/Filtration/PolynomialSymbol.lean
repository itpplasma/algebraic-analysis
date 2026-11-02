module
public import AlgebraicAnalysis.Filtration.PolynomialPresentation
public import AlgebraicAnalysis.Filtration.SymbolDomain
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section

/-!
# Injective polynomial presentations from dual coordinates

Let `φ` be a filtration of the `k`-algebra `D` with polynomial generators
`ι : A →ₐ[k] D`, `y₁, …, y_r` (`RingFiltration.PolynomialGenerators`), so that
`A[ξ₁, …, ξ_r] ↠ gr D`, `a ξ^α ↦ [ι(a) y^α]`. Suppose there are dual
coordinates `x₁, …, x_r ∈ A` with `y_i ι(xⱼ) - ι(xⱼ) y_i = δᵢⱼ`, and `ι` is
injective. If `k` is a field of characteristic zero, the presentation is
injective (`PolynomialGenerators.presentation_sym_injective`), so
`gr D ≅ A[ξ]` (`PolynomialGenerators.gradedSymbol`), and `D` is a domain when
`A` is (`PolynomialGenerators.isDomain`).

Examples: rings of differential operators `D_k(R)` with a coordinate frame
(`DifferentialOperators.IsCoordinateFrame`), and the Weyl algebra.

## Proof

Commutation with `ι(xⱼ)` acts on symbols as `∂/∂ξⱼ`: for `g` homogeneous of
degree `n + 1`, `[ev g, ι(xⱼ)] ≡ ev (∂g/∂ξⱼ)` below degree `n`
(`PolynomialGenerators.commutator_polynomialEval_sub_mem_below`). On an
ordered monomial `y_{i₁} ⋯ y_{i_m}` the commutator deletes one factor `yⱼ` at
a time, and the order of the remaining factors does not matter modulo lower
degree because `gr D` is commutative (`list_prod_commutator_sub_mem_below`).

If `ev g` lies below degree `n + 1`, then so does `[ev g, ι(xⱼ)]` below
degree `n` (`ι(xⱼ)` has degree `0`), hence `∂g/∂ξⱼ = 0` by induction, and
Euler's identity `(n + 1) g = ∑ⱼ ξⱼ ∂g/∂ξⱼ` gives `g = 0`. In degree zero,
`ev a = ι(a)`, which vanishes only for `a = 0`.

The argument is AA-native; compare [McConnell–Robson, *Noncommutative
Noetherian Rings*, 15.1.20] for `D_k(R)` with étale coordinates.
-/

namespace AlgebraicAnalysis.RingFiltration

open MvPolynomial

section List

variable {k A σ : Type*} [CommRing k] [Ring A] [Algebra k A] [DecidableEq σ]
variable (φ : RingFiltration k A)

private theorem mul_mem_below_pred {y e : A} (hy : y ∈ φ.F 1) {m : ℕ} (he : e ∈ φ.below (m - 1)) :
    y * e ∈ φ.below m := by
  cases m with
  | zero =>
      rw [below_zero, Submodule.mem_bot] at he ⊢
      rw [he, mul_zero]
  | succ m => simpa [add_comm] using φ.mul_mem_below_right hy he

/-- **Commutator with an ordered monomial.** Let `y_i ∈ F 1` and let `c`
satisfy `y_i c - c y_i = δᵢⱼ`. If the associated graded module is
commutative, then for every list `l`, the commutator of `c` with
`y_{l₁} ⋯ y_{l_m}` is `(count j l)` times the product with one `y_j`
deleted, modulo `F (m - 2)`. -/
theorem list_prod_commutator_sub_mem_below (hφ : φ.GrCommutative) {y : σ → A}
    (hy : ∀ i, y i ∈ φ.F 1) {c : A} {j : σ}
    (hc : ∀ i, y i * c - c * y i = if i = j then 1 else 0) (l : List σ) :
    (l.map y).prod * c - c * (l.map y).prod - l.count j • ((l.erase j).map y).prod ∈
      φ.below (l.length - 1) := by
  induction l with
  | nil => simp
  | cons i l ih =>
      set E := (l.map y).prod * c - c * (l.map y).prod - l.count j • ((l.erase j).map y).prod
      have hE : y i * E ∈ φ.below l.length := φ.mul_mem_below_pred (hy i) ih
      simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.add_sub_cancel]
      by_cases hij : i = j
      · subst hij
        rw [List.count_cons_self, List.erase_cons_head]
        have key : y i * (l.map y).prod * c - c * (y i * (l.map y).prod) -
              (l.count i + 1) • (l.map y).prod =
            y i * E + l.count i • (y i * ((l.erase i).map y).prod - (l.map y).prod) +
              (y i * c - c * y i - 1) * (l.map y).prod := by
          simp only [E, mul_sub, mul_smul_comm, smul_sub, add_smul, one_smul, sub_mul, one_mul]
          noncomm_ring
        rw [key, hc]
        simp only [↓reduceIte, sub_self, zero_mul, add_zero]
        refine add_mem hE ?_
        by_cases hmem : i ∈ l
        · refine Submodule.smul_of_tower_mem _ _ ?_
          have hperm := φ.list_prod_sub_mem_below_of_perm hφ y (fun _ => 1) hy
            (List.perm_cons_erase hmem).symm
          have hlen : 1 + (l.length - 1) = l.length := by
            have := List.length_pos_of_mem hmem
            omega
          simpa only [List.map_cons, List.prod_cons, List.map_const', List.sum_cons,
            List.sum_replicate, smul_eq_mul, mul_one, List.length_erase_of_mem hmem,
            hlen] using hperm
        · rw [List.count_eq_zero_of_not_mem hmem, zero_smul]
          exact zero_mem _
      · rw [List.count_cons_of_ne hij, List.erase_cons_tail (by simpa using hij)]
        simp only [List.map_cons, List.prod_cons]
        have key : y i * (l.map y).prod * c - c * (y i * (l.map y).prod) -
              l.count j • (y i * ((l.erase j).map y).prod) =
            y i * E + (y i * c - c * y i) * (l.map y).prod := by
          simp only [E, mul_sub, mul_smul_comm]
          noncomm_ring
        rw [key, hc]
        simp only [hij, ↓reduceIte, zero_mul, add_zero]
        exact hE

end List

/-! ## Monomials -/

section Monomial

variable {σ : Type*} [DecidableEq σ]

theorem count_monomialList (α : σ →₀ ℕ) (j : σ) : (monomialList α).count j = α j := by
  rw [monomialList, ← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]

/-- Deleting one `j` from the variable list of `X^α` lists `X^(α - eⱼ)`. -/
theorem monomialList_erase_perm {α : σ →₀ ℕ} {j : σ} (hj : α j ≠ 0) :
    ((monomialList α).erase j).Perm (monomialList (α - Finsupp.single j 1)) := by
  have hα : α = Finsupp.single j 1 + (α - Finsupp.single j 1) := by
    ext i
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs with h
    · subst h
      omega
    · simp
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_erase, monomialList, monomialList,
    Multiset.coe_toList, Multiset.coe_toList]
  conv_lhs => rw [hα]
  rw [map_add, Finsupp.toMultiset_single, one_smul, Multiset.singleton_add,
    Multiset.erase_cons_head]

end Monomial

section Presentation

variable {k A D σ : Type*} [CommRing k] [CommRing A] [Algebra k A] [Ring D] [Algebra k D]
  [DecidableEq σ] {φ : RingFiltration k D}

/-- On an ordered monomial `y^α`, commutation with `c` (where
`y_i c - c y_i = δᵢⱼ`) is `αⱼ y^(α - eⱼ)` below degree `|α| - 1`. -/
theorem monomialProd_commutator_sub_mem_below (hφ : φ.GrCommutative) {y : σ → D}
    (hy : ∀ i, y i ∈ φ.F 1) {c : D} {j : σ}
    (hc : ∀ i, y i * c - c * y i = if i = j then 1 else 0) (α : σ →₀ ℕ) :
    monomialProd y α * c - c * monomialProd y α - α j • monomialProd y (α - Finsupp.single j 1) ∈
      φ.below (Finsupp.weight 1 α - 1) := by
  have hl := φ.list_prod_commutator_sub_mem_below hφ hy hc (monomialList α)
  rw [count_monomialList, length_monomialList] at hl
  by_cases hj : α j = 0
  · simpa [hj, monomialProd] using hl
  have hperm := φ.list_prod_sub_mem_below_of_perm hφ _ (fun _ => 1) hy
    (monomialList_erase_perm hj)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, List.length_erase,
    length_monomialList] at hperm
  have hmem : j ∈ monomialList α := List.count_pos_iff.mp (by rw [count_monomialList]; omega)
  simp only [hmem, ↓reduceIte] at hperm
  have h := add_mem hl (Submodule.smul_of_tower_mem _ (α j) hperm)
  convert h using 1
  simp only [monomialProd, smul_sub]
  abel

namespace PolynomialGenerators

variable [Fintype σ] {ι : A →ₐ[k] D} {y : σ → D} (H : φ.PolynomialGenerators ι y)
  {x : σ → A} (hxy : ∀ i j, y i * ι (x j) - ι (x j) * y i = if i = j then 1 else 0)
include H hxy

/-- **Commutation with a dual coordinate differentiates the symbol.** For `g`
homogeneous of degree `n + 1`, `[ev g, ι(xⱼ)] - ev (∂g/∂ξⱼ)` lies below
degree `n`, where `ev (a ξ^α) = ι(a) y^α`. -/
theorem commutator_polynomialEval_sub_mem_below {n : ℕ} {g : MvPolynomial σ A}
    (hg : g.IsHomogeneous (n + 1)) (j : σ) :
    polynomialEval ι y g * ι (x j) - ι (x j) * polynomialEval ι y g -
      polynomialEval ι y (pderiv j g) ∈ φ.below n := by
  rw [← support_sum_monomial_coeff g, map_sum, map_sum, map_sum, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hdeg : Finsupp.weight 1 α - 1 = n := by
    rw [hg (mem_support_iff.mp hα)]
    rfl
  have hm := monomialProd_commutator_sub_mem_below H.grCommutative H.gen_mem
    (fun i => hxy i j) α
  rw [hdeg] at hm
  have h := φ.mul_mem_below_right (H.map_mem (g.coeff α)) hm
  rw [zero_add] at h
  convert h using 1
  have hc : ι (g.coeff α) * ι (x j) = ι (x j) * ι (g.coeff α) := by
    rw [← map_mul, mul_comm, map_mul]
  rw [pderiv_monomial, polynomialEval_monomial, polynomialEval_monomial, map_mul, map_natCast,
    mul_sub, mul_sub, nsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← hc, mul_assoc,
    mul_assoc]
  congr 1
  rw [mul_assoc, Nat.cast_comm]

end PolynomialGenerators

end Presentation

section Injective

variable {k A D σ : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A] [Ring D]
  [Algebra k D] [DecidableEq σ] [Fintype σ] {φ : RingFiltration k D}

namespace PolynomialGenerators

variable {ι : A →ₐ[k] D} {y : σ → D} (H : φ.PolynomialGenerators ι y)
  {x : σ → A} (hxy : ∀ i j, y i * ι (x j) - ι (x j) * y i = if i = j then 1 else 0)
  (hι : Function.Injective ι)
include H hxy hι

/-- **Injectivity of the symbol.** If `g` is homogeneous of degree `n` and
`ev g` lies below degree `n`, then `g = 0`. -/
theorem eq_zero_of_polynomialEval_mem_below :
    ∀ n, ∀ g : MvPolynomial σ A, g.IsHomogeneous n → polynomialEval ι y g ∈ φ.below n → g = 0 := by
  intro n
  induction n with
  | zero =>
      intro g hg hmem
      by_contra hg0
      obtain ⟨a, rfl⟩ : ∃ a, g = C a :=
        ⟨_, totalDegree_eq_zero_iff_eq_C.mp (hg.totalDegree hg0)⟩
      rw [C_apply, polynomialEval_monomial, monomialProd_zero, mul_one, below_zero,
        Submodule.mem_bot, ← map_zero ι] at hmem
      exact hg0 (by rw [hι hmem, C_0])
  | succ n ih =>
      intro g hg hmem
      have hpd : ∀ j, pderiv j g = 0 := by
        intro j
        refine ih _ (by simpa using hg.pderiv (i := j)) ?_
        have hcomm : polynomialEval ι y g * ι (x j) - ι (x j) * polynomialEval ι y g ∈
            φ.below n := by
          simpa using H.grCommutative hmem (H.map_mem (x j))
        simpa using sub_mem hcomm (H.commutator_polynomialEval_sub_mem_below hxy hg j)
      have heuler := hg.sum_X_mul_pderiv
      simp only [hpd, mul_zero, Finset.sum_const_zero] at heuler
      have hne : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      rw [← Nat.cast_smul_eq_nsmul k] at heuler
      rw [← inv_smul_smul₀ hne g, ← heuler, smul_zero]

/-- The polynomial presentation `A[ξ] ↠ gr D` is injective in every degree. -/
theorem presentation_sym_injective (n : ℕ) : Function.Injective (H.presentation.sym n) := by
  refine (injective_iff_map_eq_zero _).mpr fun g hg => ?_
  rw [presentation_sym, Submodule.Quotient.mk_eq_zero, mem_belowInF] at hg
  exact Subtype.ext (H.eq_zero_of_polynomialEval_mem_below hxy hι n g.1
    (mem_polynomialGrading.mp g.2) hg)

/-- **`gr D ≅ A[ξ₁, …, ξ_r]`**, graded by total degree. -/
noncomputable def gradedSymbol : φ.GradedSymbol (polynomialGrading σ k A) :=
  H.presentation.toGradedSymbol (H.presentation_sym_injective hxy hι)

/-- **`D` is a domain** if `A` is. -/
theorem isDomain [IsDomain A] : IsDomain D :=
  (H.gradedSymbol hxy hι).isDomain (mem_polynomialGrading.mpr (isHomogeneous_one σ A))

end PolynomialGenerators

end Injective

end AlgebraicAnalysis.RingFiltration
