/- SPDX-License-Identifier: Apache-2.0 -/

module
public import AlgebraicAnalysis.Enveloping.Presentation
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section

/-!
Oracles for the PBW filtration on the abelian Lie algebra `k^m`.

The bracket of `L = Fin m → k` is the commutator of the commutative ring, so it is zero.
The map `e_i ↦ X_i` extends to a surjective algebra map `π : U(L) → k[X₀, …, X_{m-1}]`.

* Filtration oracle: the PBW piece `Fₙ` of `k[X]` equals the polynomials of total degree
  at most `n` (`restrictTotalDegree`). This is a characterization by
  `MvPolynomial.totalDegree`, which does not mention products of Lie elements.
* Dimension oracle: the deviation bound for this `π` is `m = dim k^m`, the value of
  `ringKrullDim k[X₀, …, X_{m-1}]`.
-/

namespace AlgebraicAnalysisTest.Enveloping

open AlgebraicAnalysis AlgebraicAnalysis.Enveloping MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type*} [Field k] {m : ℕ}

/-- The coordinate linear form `x ↦ ∑ xᵢ Xᵢ` on the abelian Lie algebra `k^m`. -/
noncomputable def linearForm : (Fin m → k) →ₗ⁅k⁆ MvPolynomial (Fin m) k where
  toFun x := ∑ i, C (x i) * X i
  map_add' x y := by
    simp [add_mul, Finset.sum_add_distrib, C_add]
  map_smul' c x := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, C_mul, smul_eq_C_mul, mul_assoc,
      Finset.mul_sum]
  map_lie' {x y} := by
    have h : ⁅x, y⁆ = (0 : Fin m → k) := by rw [Ring.lie_def, mul_comm, sub_self]
    have h' : ∀ a b : MvPolynomial (Fin m) k, ⁅a, b⁆ = 0 := fun a b => by
      rw [Ring.lie_def, mul_comm, sub_self]
    rw [h, h']
    simp

theorem linearForm_apply (x : Fin m → k) : linearForm x = ∑ i, C (x i) * X i :=
  rfl

/-- The algebra map `π : U(k^m) → k[X₀, …, X_{m-1}]` with `e_i ↦ X_i`. -/
noncomputable def piAb : UniversalEnvelopingAlgebra k (Fin m → k) →ₐ[k] MvPolynomial (Fin m) k :=
  UniversalEnvelopingAlgebra.lift k linearForm

/-- The image of a Lie element under `π` is its linear form. -/
theorem gen_piAb (x : Fin m → k) : gen piAb x = linearForm x :=
  UniversalEnvelopingAlgebra.lift_ι_apply k linearForm x

theorem piAb_ι_single (i : Fin m) :
    piAb (UniversalEnvelopingAlgebra.ι k (Pi.single i (1 : k))) = X i := by
  rw [piAb, UniversalEnvelopingAlgebra.lift_ι_apply, linearForm_apply]
  simp [Pi.single_apply]

/-- `π` is surjective: the image is a subalgebra containing every `X i`. -/
theorem piAb_surjective : Function.Surjective (piAb (k := k) (m := m)) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨algebraMap k _ a, by simp⟩
  | add p q hp hq =>
    obtain ⟨u, rfl⟩ := hp
    obtain ⟨v, rfl⟩ := hq
    exact ⟨u + v, map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨u, rfl⟩ := hp
    exact ⟨u * UniversalEnvelopingAlgebra.ι k (Pi.single i 1), by
      rw [map_mul, piAb_ι_single]⟩

/-- Each generator's image has total degree at most one. -/
theorem totalDegree_gen_le (x : Fin m → k) : (gen piAb x).totalDegree ≤ 1 := by
  rw [gen_piAb, linearForm_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_X]

theorem totalDegree_wordProd_le (w : List (Fin m → k)) :
    (wordProd piAb w).totalDegree ≤ w.length := by
  induction w with
  | nil => simp [wordProd_nil]
  | cons x w ih =>
    rw [wordProd_cons, List.length_cons]
    refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_gen_le x
    omega

/-- Products of at most `n` Lie elements lie in the total-degree-`n` polynomials. -/
theorem pbwPiece_le_restrict (n : ℕ) :
    pbwPiece piAb n ≤ restrictTotalDegree (Fin m) k n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe, mem_restrictTotalDegree]
  exact (totalDegree_wordProd_le w).trans hw

/-- Each generator `X i` lies in `F₁`. -/
theorem X_mem_pbwPiece_one (i : Fin m) : (X i : MvPolynomial (Fin m) k) ∈ pbwPiece piAb 1 := by
  rw [← piAb_ι_single i]
  exact gen_mem_pbwPiece_one piAb _

/-- The monomial `X^d` lies in `F_{|d|}`, where `|d|` is the total degree of `d`. -/
theorem monomial_mem_pbwPiece (d : Fin m →₀ ℕ) :
    monomial d (1 : k) ∈ pbwPiece piAb (d.sum fun _ e => e) := by
  induction d using Finsupp.induction_linear with
  | zero =>
    rw [Finsupp.sum_zero_index, show (monomial 0 (1 : k) : MvPolynomial (Fin m) k) = 1 from rfl]
    exact one_mem_pbwPiece piAb 0
  | add f g hf hg =>
    rw [show (monomial (f + g) (1 : k) : MvPolynomial (Fin m) k) = monomial f 1 * monomial g 1 by
      rw [monomial_mul_monomial, one_mul], Finsupp.sum_add_index']
    · exact mul_mem_pbwPiece piAb hf hg
    · intro _; rfl
    · intro _ _ _; rfl
  | single i a =>
    rw [Finsupp.sum_single_index rfl, ← X_pow_eq_monomial]
    induction a with
    | zero => simpa using one_mem_pbwPiece piAb 0
    | succ a ih =>
      rw [pow_succ]
      exact mul_mem_pbwPiece piAb ih (X_mem_pbwPiece_one i)

/-- Polynomials of total degree at most `n` lie in `Fₙ`. -/
theorem restrict_le_pbwPiece (n : ℕ) :
    restrictTotalDegree (Fin m) k n ≤ pbwPiece piAb n := by
  intro p hp
  rw [mem_restrictTotalDegree] at hp
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdeg : (d.sum fun _ e => e) ≤ n := (le_totalDegree hd).trans hp
  have hc : monomial d (p.coeff d) = (p.coeff d) • monomial d (1 : k) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hc]
  exact Submodule.smul_mem _ _ (pbwPiece_mono piAb hdeg (monomial_mem_pbwPiece d))

/-- The total-degree filtration is the PBW filtration of the abelian Lie algebra `k^m`. -/
theorem pbwPiece_eq_restrictTotalDegree (n : ℕ) :
    pbwPiece piAb n = restrictTotalDegree (Fin m) k n :=
  le_antisymm (pbwPiece_le_restrict n) (restrict_le_pbwPiece n)

/-- Noetherianity of the polynomial ring through the general theorem. -/
example : IsNoetherianRing (MvPolynomial (Fin m) k) :=
  isNoetherianRing_of_surjective piAb piAb_surjective

/-- Right deviation of `k[X₀, …, X_{m-1}]` is at most `m`, the dimension of `k^m`. -/
example : Module.DevLE (MvPolynomial (Fin m) k)ᵐᵒᵖ m (MvPolynomial (Fin m) k) := by
  have h := devLE_right_of_surjective (k := k) (L := Fin m → k) piAb piAb_surjective
  rwa [Module.finrank_fin_fun] at h

/-- The same bound on the left, through the general theorem. -/
example : Module.DevLE (MvPolynomial (Fin m) k) m (MvPolynomial (Fin m) k) := by
  have h := devLE_left_of_surjective (k := k) (L := Fin m → k) piAb piAb_surjective
  rwa [Module.finrank_fin_fun] at h

/-- The universal enveloping algebra itself is Noetherian on both sides, with deviation
`dim L`. -/
example {L : Type*} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] :
    IsNoetherianRing (UniversalEnvelopingAlgebra k L) :=
  isNoetherianRing_of_surjective (AlgHom.id k _) Function.surjective_id

#print axioms pbwPiece_eq_restrictTotalDegree
#print axioms AlgebraicAnalysis.Enveloping.isNoetherian_right_of_surjective
#print axioms AlgebraicAnalysis.Enveloping.devLE_right_of_surjective
#print axioms AlgebraicAnalysis.Enveloping.devLE_left_of_surjective
#print axioms AlgebraicAnalysis.Enveloping.wordProd_sub_mem_pbwPiece

end AlgebraicAnalysisTest.Enveloping
