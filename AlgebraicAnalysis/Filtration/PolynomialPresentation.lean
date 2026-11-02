module
public import AlgebraicAnalysis.Filtration.SymbolPresentation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-!
# Polynomial presentations of a commutative associated graded ring

Let `φ` be an ascending filtration of a `k`-algebra `D` whose associated graded
module is commutative (`RingFiltration.GrCommutative`: `x y - y x` has degree
below `i + j` for `x ∈ F i`, `y ∈ F j`). Suppose a commutative `k`-algebra `A`
maps onto `F 0` by `ι : A →ₐ[k] D`, and finitely many elements `y₁, …, y_r` of
`F 1` generate the filtration in degree one:
`F (n + 1) ⊆ F n + F n y₁ + ⋯ + F n y_r`. Then the polynomial ring
`G = A[X₁, …, X_r]`, graded by total degree, maps onto `gr D` by
`a X^α ↦ [ι(a) y^α]`. This is a surjective symbol presentation
(`RingFiltration.SymbolPresentation`), so `D` is right and left Noetherian
when `A` is Noetherian, and the ideal lattices of `D` have deviation at most
`dim A + r` when `A` has finite Krull dimension.

The monomial `y^α` is the product of the `y_i` in the order of the list
`(Finsupp.toMultiset α).toList`. The order does not matter modulo lower
degree, by commutativity of `gr D` (`list_prod_sub_mem_below_of_perm`).

This is the generic layer for rings of differential operators `D_k(A)` (with
`y_i` coordinate derivations), and for enveloping-type algebras (with `A = k`).
Injectivity of the presentation is neither claimed nor needed.

## Main definitions and results

* `RingFiltration.GrCommutative`: the associated graded module is commutative.
* `RingFiltration.list_prod_sub_mem_below_of_perm`: in a filtration with
  commutative associated graded, permuting a product changes it only in lower
  degree.
* `RingFiltration.polynomialGrading`: total-degree grading of `A[X_σ]` by
  `k`-submodules, with its `GradedAlgebra` instance.
* `RingFiltration.PolynomialGenerators`: the hypotheses above.
* `RingFiltration.PolynomialGenerators.presentation`: the surjective symbol
  presentation `A[X_σ] ↠ gr D`.
* `PolynomialGenerators.isNoetherian_right`, `isNoetherianRing`,
  `devLE_right`, `devLE_left`, `devLEOmega_right`, `devLEOmega_left`.

## References

[MR] J. C. McConnell and J. C. Robson, *Noncommutative Noetherian Rings*,
1.6.9 and 6.5.6. The presentation-by-generators argument is AA-native.
-/

namespace AlgebraicAnalysis

open MvPolynomial

namespace RingFiltration

section Commutative

variable {R D : Type*} [CommRing R] [Ring D] [Algebra R D] (φ : RingFiltration R D)

/-- The associated graded module of `φ` is commutative: for `x ∈ F i` and
`y ∈ F j`, the commutator `x y - y x` lies below degree `i + j`. -/
def GrCommutative : Prop :=
  ∀ ⦃i j : ℕ⦄ ⦃x y : D⦄, x ∈ φ.F i → y ∈ φ.F j → x * y - y * x ∈ φ.below (i + j)

/-- The predecessor piece lies in the piece itself. -/
theorem below_le (n : ℕ) : φ.below n ≤ φ.F n := by
  cases n with
  | zero => exact bot_le
  | succ n => exact φ.mono (Nat.le_succ n)

/-- Left multiplication of a below-degree-`i` element by a degree-`j` element. -/
theorem mul_mem_below_left {x y : D} {i j : ℕ} (hx : x ∈ φ.below i) (hy : y ∈ φ.F j) :
    x * y ∈ φ.below (i + j) :=
  φ.below_mul_le i j (Submodule.mul_mem_mul hx hy)

/-- Right multiplication of a degree-`i` element by a below-degree-`j` element. -/
theorem mul_mem_below_right {x y : D} {i j : ℕ} (hx : x ∈ φ.F i) (hy : y ∈ φ.below j) :
    x * y ∈ φ.below (i + j) :=
  φ.mul_below_le i j (Submodule.mul_mem_mul hx hy)

/-- A product of elements `f i ∈ F (d i)` along a list has degree at most the
sum of the degrees. -/
theorem list_prod_mem {ι : Type*} (f : ι → D) (d : ι → ℕ) (hf : ∀ i, f i ∈ φ.F (d i))
    (l : List ι) : (l.map f).prod ∈ φ.F (l.map d).sum := by
  induction l with
  | nil => simpa using φ.one_mem
  | cons a l ih => simpa using φ.mul_mem_add (hf a) ih

/-- **Products commute modulo lower degree.** If the associated graded module
is commutative, two products of the same factors `f i ∈ F (d i)` in permuted
orders differ by an element below the total degree. -/
theorem list_prod_sub_mem_below_of_perm (hφ : φ.GrCommutative) {ι : Type*} (f : ι → D)
    (d : ι → ℕ) (hf : ∀ i, f i ∈ φ.F (d i)) {l l' : List ι} (h : l.Perm l') :
    (l.map f).prod - (l'.map f).prod ∈ φ.below (l.map d).sum := by
  induction h with
  | nil => simp
  | cons a _ ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [← mul_sub]
      exact φ.mul_mem_below_right (hf a) ih
  | swap a b l =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [← mul_assoc, ← mul_assoc, ← sub_mul, ← add_assoc]
      exact φ.mul_mem_below_left (hφ (hf b) (hf a)) (φ.list_prod_mem f d hf l)
  | trans h₁ _ ih₁ ih₂ =>
      rw [(h₁.map d).sum_eq] at ih₁ ⊢
      simpa using add_mem ih₁ ih₂

end Commutative

section Presentation

variable {k A D σ : Type*} [CommRing k] [CommRing A] [Algebra k A] [Ring D] [Algebra k D]

/-- The total-degree grading of the polynomial ring `A[X_σ]`, by `k`-submodules:
the degree-`n` piece is the `A`-submodule of homogeneous polynomials of degree
`n`, with scalars restricted to `k`. The coefficient ring `A` lies in degree `0`. -/
noncomputable def polynomialGrading (σ k A : Type*) [CommRing k] [CommRing A] [Algebra k A] (n : ℕ) :
    Submodule k (MvPolynomial σ A) :=
  (homogeneousSubmodule σ A n).restrictScalars k

theorem mem_polynomialGrading {n : ℕ} {f : MvPolynomial σ A} :
    f ∈ polynomialGrading σ k A n ↔ f.IsHomogeneous n :=
  mem_homogeneousSubmodule n f

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The total-degree grading of `A[X_σ]` is a graded `k`-algebra; the data are
those of Mathlib's `MvPolynomial.gradedAlgebra` over `A`. -/
noncomputable instance : GradedAlgebra (polynomialGrading σ k A) where
  one_mem := SetLike.GradedOne.one_mem (A := homogeneousSubmodule σ A)
  mul_mem := fun _ _ _ _ ha hb => SetLike.GradedMul.mul_mem (A := homogeneousSubmodule σ A) ha hb
  decompose' := DirectSum.decompose (homogeneousSubmodule σ A)
  left_inv := DirectSum.Decomposition.left_inv (ℳ := homogeneousSubmodule σ A)
  right_inv := DirectSum.Decomposition.right_inv (ℳ := homogeneousSubmodule σ A)

/-- The variables of the monomial `X^α`, listed with multiplicity in a fixed
(noncanonical) order. -/
noncomputable def monomialList (α : σ →₀ ℕ) : List σ :=
  (Finsupp.toMultiset α).toList

theorem length_monomialList (α : σ →₀ ℕ) : (monomialList α).length = Finsupp.weight 1 α := by
  simp [monomialList, Finsupp.card_toMultiset, Finsupp.weight_apply, Finsupp.sum]

theorem monomialList_add_perm (α β : σ →₀ ℕ) :
    (monomialList α ++ monomialList β).Perm (monomialList (α + β)) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, monomialList, monomialList, monomialList,
    Multiset.coe_toList, Multiset.coe_toList, Multiset.coe_toList, map_add]

/-- The ordered monomial `y^α = ∏ y_i` over `monomialList α`. -/
noncomputable def monomialProd (y : σ → D) (α : σ →₀ ℕ) : D :=
  ((monomialList α).map y).prod

@[simp] theorem monomialProd_zero (y : σ → D) : monomialProd y 0 = 1 := by
  simp [monomialProd, monomialList]

@[simp] theorem monomialProd_single (y : σ → D) (i : σ) :
    monomialProd y (Finsupp.single i 1) = y i := by
  simp [monomialProd, monomialList]

/-- The evaluation `A[X_σ] → D`, `a X^α ↦ ι(a) y^α`, as a `k`-linear map. -/
noncomputable def polynomialEval (ι : A →ₐ[k] D) (y : σ → D) : MvPolynomial σ A →ₗ[k] D :=
  (Finsupp.lsum ℕ fun α => (LinearMap.mulRight k (monomialProd y α)).comp ι.toLinearMap) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem polynomialEval_monomial (ι : A →ₐ[k] D) (y : σ → D) (α : σ →₀ ℕ) (a : A) :
    polynomialEval ι y (monomial α a) = ι a * monomialProd y α := by
  simp [polynomialEval, monomial]

variable (φ : RingFiltration k D)

/-- An ordered monomial `y^α` in elements of degree one has degree `|α|`. -/
theorem monomialProd_mem {y : σ → D} (hy : ∀ i, y i ∈ φ.F 1) (α : σ →₀ ℕ) :
    monomialProd y α ∈ φ.F (Finsupp.weight 1 α) := by
  have h := φ.list_prod_mem y (fun _ => 1) hy (monomialList α)
  rwa [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, length_monomialList] at h

/-- The image of a homogeneous polynomial of degree `n` has degree `n`. -/
theorem polynomialEval_mem {ι : A →ₐ[k] D} (hι : ∀ a, ι a ∈ φ.F 0) {y : σ → D}
    (hy : ∀ i, y i ∈ φ.F 1) {n : ℕ} {f : MvPolynomial σ A} (hf : f.IsHomogeneous n) :
    polynomialEval ι y f ∈ φ.F n := by
  rw [← support_sum_monomial_coeff f, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [polynomialEval_monomial]
  have h := φ.mul_mem_add (hι (f.coeff α)) (φ.monomialProd_mem hy α)
  rwa [zero_add, hf (mem_support_iff.mp hα)] at h

/-- **Monomials multiply modulo lower degree.**
`ι(ab) y^(α+β) ≡ ι(a) y^α ι(b) y^β` below degree `|α| + |β|`. -/
theorem monomial_mul_sub_mem_below (hφ : φ.GrCommutative) {ι : A →ₐ[k] D}
    (hι : ∀ a, ι a ∈ φ.F 0) {y : σ → D} (hy : ∀ i, y i ∈ φ.F 1) (α β : σ →₀ ℕ) (a b : A) :
    ι (a * b) * monomialProd y (α + β) - ι a * monomialProd y α * (ι b * monomialProd y β) ∈
      φ.below (Finsupp.weight 1 α + Finsupp.weight 1 β) := by
  have hperm := φ.list_prod_sub_mem_below_of_perm hφ y (fun _ => 1) hy
    (monomialList_add_perm α β).symm
  rw [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, length_monomialList,
    map_add] at hperm
  have h₁ := φ.mul_mem_below_right (φ.mul_mem_add (hι a) (hι b)) hperm
  have h₂ := φ.mul_mem_below_left (φ.mul_mem_below_right (hι a)
    (hφ (hι b) (φ.monomialProd_mem hy α))) (φ.monomialProd_mem hy β)
  simp only [zero_add] at h₁ h₂
  have key : ι (a * b) * monomialProd y (α + β) -
      ι a * monomialProd y α * (ι b * monomialProd y β) =
      ι a * ι b * (monomialProd y (α + β) - ((monomialList α ++ monomialList β).map y).prod) +
        ι a * (ι b * monomialProd y α - monomialProd y α * ι b) * monomialProd y β := by
    simp only [List.map_append, List.prod_append, map_mul, monomialProd]
    noncomm_ring
  rw [key]
  exact add_mem h₁ h₂

/-- **The evaluation is multiplicative modulo lower degree** on homogeneous
polynomials: `ev(g h) ≡ ev(g) ev(h)` below degree `i + j`. -/
theorem polynomialEval_mul_sub_mem_below (hφ : φ.GrCommutative) {ι : A →ₐ[k] D}
    (hι : ∀ a, ι a ∈ φ.F 0) {y : σ → D} (hy : ∀ i, y i ∈ φ.F 1) {i j : ℕ}
    {g h : MvPolynomial σ A} (hg : g.IsHomogeneous i) (hh : h.IsHomogeneous j) :
    polynomialEval ι y (g * h) - polynomialEval ι y g * polynomialEval ι y h ∈
      φ.below (i + j) := by
  rw [← support_sum_monomial_coeff g, ← support_sum_monomial_coeff h, Finset.sum_mul_sum]
  simp only [map_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun α hα => Submodule.sum_mem _ fun β hβ => ?_
  rw [monomial_mul_monomial, polynomialEval_monomial, polynomialEval_monomial,
    polynomialEval_monomial]
  have hm := φ.monomial_mul_sub_mem_below hφ hι hy α β (g.coeff α) (h.coeff β)
  rwa [hg (mem_support_iff.mp hα), hh (mem_support_iff.mp hβ)] at hm

/-- The hypotheses for a polynomial presentation of `gr D`: the associated
graded module is commutative, `ι : A →ₐ[k] D` maps onto `F 0`, the elements
`y_i` have degree one, and they generate the filtration in degree one,
`F (n + 1) ⊆ F n + ∑ᵢ F n · y_i`. -/
structure PolynomialGenerators [Fintype σ] (ι : A →ₐ[k] D) (y : σ → D) : Prop where
  /-- The associated graded module is commutative. -/
  grCommutative : φ.GrCommutative
  /-- `ι(A)` lies in degree `0`. -/
  map_mem : ∀ a, ι a ∈ φ.F 0
  /-- Every element of degree `0` is in the image of `ι`. -/
  exists_map_eq : ∀ x ∈ φ.F 0, ∃ a, ι a = x
  /-- The generators have degree one. -/
  gen_mem : ∀ i, y i ∈ φ.F 1
  /-- Generation in degree one: `F (n + 1) ⊆ F n + ∑ᵢ F n · y_i`. -/
  exists_sum_mul : ∀ n, ∀ x ∈ φ.F (n + 1),
    ∃ z : σ → D, (∀ i, z i ∈ φ.F n) ∧ x - ∑ i, z i * y i ∈ φ.F n

namespace PolynomialGenerators

variable {φ} [Fintype σ] {ι : A →ₐ[k] D} {y : σ → D} (H : φ.PolynomialGenerators ι y)
include H

/-- Every element of degree `n` agrees, below degree `n`, with the image of a
homogeneous polynomial of degree `n`. -/
theorem exists_polynomialEval_sub_mem_below :
    ∀ n, ∀ x ∈ φ.F n, ∃ g : MvPolynomial σ A, g.IsHomogeneous n ∧
      x - polynomialEval ι y g ∈ φ.below n := by
  intro n
  induction n with
  | zero =>
      intro x hx
      obtain ⟨a, rfl⟩ := H.exists_map_eq x hx
      refine ⟨C a, isHomogeneous_C σ a, ?_⟩
      rw [C_apply, polynomialEval_monomial, monomialProd_zero, mul_one, sub_self]
      exact zero_mem _
  | succ n ih =>
      intro x hx
      obtain ⟨z, hz, hxz⟩ := H.exists_sum_mul n x hx
      choose g hg hgz using fun i => ih (z i) (hz i)
      refine ⟨∑ i, g i * X i,
        IsHomogeneous.sum _ _ _ fun i _ => (hg i).mul (isHomogeneous_X A i), ?_⟩
      have hX : ∀ i, polynomialEval ι y (X i) = y i := by
        intro i
        rw [X, polynomialEval_monomial, map_one, one_mul, monomialProd_single]
      have key : x - polynomialEval ι y (∑ i, g i * X i) =
          (x - ∑ i, z i * y i) + ∑ i, (z i - polynomialEval ι y (g i)) * y i -
            ∑ i, (polynomialEval ι y (g i * X i) - polynomialEval ι y (g i) * y i) := by
        simp only [map_sum, sub_mul, Finset.sum_sub_distrib]
        abel
      rw [key]
      refine sub_mem (add_mem hxz (Submodule.sum_mem _ fun i _ => ?_))
        (Submodule.sum_mem _ fun i _ => ?_)
      · exact φ.mul_mem_below_left (hgz i) (H.gen_mem i)
      · have h := φ.polynomialEval_mul_sub_mem_below H.grCommutative H.map_mem H.gen_mem
          (hg i) (isHomogeneous_X A i)
        rwa [hX] at h

/-- The degree-`n` evaluation `𝒜ₙ → Fₙ` on homogeneous polynomials. -/
noncomputable def evalPiece (n : ℕ) : polynomialGrading σ k A n →ₗ[k] φ.F n :=
  LinearMap.codRestrict (φ.F n) ((polynomialEval ι y).comp (polynomialGrading σ k A n).subtype)
    fun g => φ.polynomialEval_mem H.map_mem H.gen_mem (mem_polynomialGrading.mp g.2)

/-- **The polynomial presentation of `gr D`.** The symbol of a homogeneous
polynomial `g` of degree `n` is the class of `ev(g)` in `Fₙ/Fₙ₋₁`. -/
noncomputable def presentation : SymbolPresentation φ (polynomialGrading σ k A) where
  sym n := (φ.belowInF n).mkQ ∘ₗ H.evalPiece n
  sym_surjective n := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨g, hg, hd⟩ := H.exists_polynomialEval_sub_mem_below n x x.2
    refine ⟨⟨g, mem_polynomialGrading.mpr hg⟩, (Submodule.Quotient.eq _).mpr ?_⟩
    rw [mem_belowInF]
    simpa [evalPiece] using neg_mem hd
  sym_mul i j g h x hx := by
    show Submodule.Quotient.mk _ = φ.gradedMul i j (Submodule.Quotient.mk _)
      (Submodule.Quotient.mk _)
    rw [gradedMul_mk]
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [mem_belowInF]
    simpa [evalPiece, hx] using φ.polynomialEval_mul_sub_mem_below H.grCommutative H.map_mem
      H.gen_mem (mem_polynomialGrading.mp g.2) (mem_polynomialGrading.mp h.2)

/-- The symbol of a homogeneous polynomial is the class of its evaluation. -/
theorem presentation_sym (n : ℕ) (g : polynomialGrading σ k A n) :
    H.presentation.sym n g = Submodule.Quotient.mk (H.evalPiece n g) := rfl

variable [IsNoetherianRing A] [Finite σ]

/-- `D` is right Noetherian if `A` is Noetherian [MR 1.6.9]. -/
theorem isNoetherian_right : IsNoetherian Dᵐᵒᵖ D := H.presentation.isNoetherian_right

/-- `D` is left Noetherian if `A` is Noetherian [MR 1.6.9]. -/
theorem isNoetherianRing : IsNoetherianRing D := H.presentation.isNoetherianRing

omit [CommRing k] [Algebra k A] [Ring D] [Algebra k D] [Fintype σ] H in
/-- If `dim A ≤ d`, then `dim A[X_σ] ≤ d + |σ|`. -/
theorem ringKrullDim_le {d : ℕ} (hA : ringKrullDim A ≤ d) :
    ringKrullDim (MvPolynomial σ A) ≤ ((d + Nat.card σ : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
  push_cast
  exact add_le_add_left hA _

omit [CommRing k] [Algebra k A] [Ring D] [Algebra k D] [Fintype σ] H in
theorem ringKrullDim_ne_top {d : ℕ} (hA : ringKrullDim A ≤ d) :
    ringKrullDim (MvPolynomial σ A) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (ringKrullDim_le hA)
  intro h
  exact ENat.natCast_ne_top _ (Option.some_injective _ h)

/-- If `dim A ≤ d`, the right ideals of `D` have deviation at most `d + r`
[MR 6.5.6]. -/
theorem devLE_right {d : ℕ} (hA : ringKrullDim A ≤ d) :
    Module.DevLE Dᵐᵒᵖ (d + Nat.card σ) D :=
  H.presentation.devLE_right _ (ringKrullDim_le hA)

/-- If `dim A ≤ d`, the left ideals of `D` have deviation at most `d + r`
[MR 6.5.6]. -/
theorem devLE_left {d : ℕ} (hA : ringKrullDim A ≤ d) :
    Module.DevLE D (d + Nat.card σ) D :=
  H.presentation.devLE_left _ (ringKrullDim_le hA)

/-- If `A` has finite Krull dimension, the right ideals of `D` have deviation
at most omega. -/
theorem devLEOmega_right {d : ℕ} (hA : ringKrullDim A ≤ d) : Module.DevLEOmega Dᵐᵒᵖ D :=
  H.presentation.devLEOmega_right (ringKrullDim_ne_top hA)

/-- If `A` has finite Krull dimension, the left ideals of `D` have deviation
at most omega. -/
theorem devLEOmega_left {d : ℕ} (hA : ringKrullDim A ≤ d) : Module.DevLEOmega D D :=
  H.presentation.devLEOmega_left (ringKrullDim_ne_top hA)

end PolynomialGenerators

end Presentation

end RingFiltration

end AlgebraicAnalysis
