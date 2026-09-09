/- SPDX-License-Identifier: Apache-2.0 -/

import HessianAlgebra.CoordinateChange

/-!
Prefix substitution and the elementary triangular-coordinate automorphism.
These are the factors used to construct inverses of finite triangular maps.
-/

noncomputable section

namespace HessianAlgebra
namespace PolynomialMap

open MvPolynomial

variable {K σ τ : Type*} [Field K]
variable [Fintype σ] [DecidableEq σ]

lemma substitute_rename_of_eq_on (e : τ → σ) (g : σ → MvPolynomial σ K)
    (hfix : ∀ j, g (e j) = X (e j)) (p : MvPolynomial τ K) :
    substitute g (rename e p) = rename e p := by
  let lhs : MvPolynomial τ K →+* MvPolynomial σ K :=
    (substitute g).comp (rename e).toRingHom
  have hlhs : lhs = (rename e : MvPolynomial τ K →ₐ[K] MvPolynomial σ K).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, substitute]
    · intro j
      simp [lhs, substitute_X, hfix]
  exact DFunLike.congr_fun hlhs p

lemma substitute_prefix_rename_of_eq_on {n i : ℕ}
    (hni : i ≤ n)
    (g : Fin n → MvPolynomial (Fin n) K)
    (hfix : ∀ j : Fin i, g (Fin.castLE hni j) = X (Fin.castLE hni j))
    (p : MvPolynomial (Fin i) K) :
    substitute g (rename (Fin.castLE hni) p) = rename (Fin.castLE hni) p := by
  exact substitute_rename_of_eq_on _ g hfix p

lemma substitute_rename_comp (e : τ → σ)
    [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial τ K) (g : σ → MvPolynomial σ K)
    (hcomp : ∀ j, g (e j) = rename e (f j))
    (p : MvPolynomial τ K) :
    substitute g (rename e p) = rename e (substitute f p) := by
  let lhs : MvPolynomial τ K →+* MvPolynomial σ K :=
    (substitute g).comp (rename e).toRingHom
  let rhs : MvPolynomial τ K →+* MvPolynomial σ K :=
    (rename e).toRingHom.comp (substitute f)
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, substitute]
    · intro j
      dsimp [lhs, rhs]
      rw [rename_X, substitute_X, substitute_X, hcomp]
  exact DFunLike.congr_fun h p

def finSuccLift {n : ℕ} (f : Fin n → MvPolynomial (Fin n) K) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) K :=
  Fin.lastCases (X (Fin.last n)) (fun i => rename Fin.castSucc (f i))

lemma finSuccLift_castSucc {n : ℕ}
    (f : Fin n → MvPolynomial (Fin n) K) (i : Fin n) :
    finSuccLift f i.castSucc = rename Fin.castSucc (f i) := by
  simp [finSuccLift]

lemma finSuccLift_last {n : ℕ}
    (f : Fin n → MvPolynomial (Fin n) K) :
    finSuccLift f (Fin.last n) = X (Fin.last n) := by
  simp [finSuccLift]

lemma finSuccLift_twoSidedInverse {n : ℕ}
    {f g : Fin n → MvPolynomial (Fin n) K}
    (hfg : TwoSidedInverse f g) :
    TwoSidedInverse (finSuccLift f) (finSuccLift g) := by
  constructor
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [finSuccLift, substitute_X]
    · rw [finSuccLift_castSucc, substitute_rename_comp Fin.castSucc g
          (finSuccLift g) (finSuccLift_castSucc g)]
      rw [hfg.compose_forward]
      simp
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [finSuccLift, substitute_X]
    · rw [finSuccLift_castSucc, substitute_rename_comp Fin.castSucc f
          (finSuccLift f) (finSuccLift_castSucc f)]
      rw [hfg.compose_reverse]
      simp

/-- Changing one coordinate by a unit multiple plus a polynomial in fixed
coordinates is a polynomial automorphism, with its explicit inverse. -/
theorem elementaryTriangular_twoSidedInverse
    (e : τ → σ) (k : σ) (he : ∀ j, e j ≠ k)
    (a : K) (ha : a ≠ 0) (p : MvPolynomial τ K) :
    let P : MvPolynomial σ K := rename e p
    let F : σ → MvPolynomial σ K := fun i =>
      if i = k then C a * X k + P else X i
    let G : σ → MvPolynomial σ K := fun i =>
      if i = k then C a⁻¹ * (X k - P) else X i
    TwoSidedInverse F G := by
  dsimp only
  let P : MvPolynomial σ K := rename e p
  let F : σ → MvPolynomial σ K := fun i =>
    if i = k then C a * X k + P else X i
  let G : σ → MvPolynomial σ K := fun i =>
    if i = k then C a⁻¹ * (X k - P) else X i
  have hfixG : ∀ j, G (e j) = X (e j) := by
    intro j
    simp [G, he j]
  have hfixF : ∀ j, F (e j) = X (e j) := by
    intro j
    simp [F, he j]
  have hPG : substitute G P = P :=
    substitute_rename_of_eq_on e G hfixG p
  have hPF : substitute F P = P :=
    substitute_rename_of_eq_on e F hfixF p
  refine ⟨?_, ?_⟩
  · intro i
    by_cases hi : i = k
    · subst i
      simp only [if_pos, map_add, map_mul, substitute_X]
      rw [show substitute G (C a) = C a by simp [substitute], hPG]
      change C a * (C a⁻¹ * (X k - P)) + P = X k
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, map_one, one_mul,
        sub_add_cancel]
    · simp [substitute_X, hi]
  · intro i
    by_cases hi : i = k
    · subst i
      simp only [if_pos, map_mul, map_sub, substitute_X]
      rw [show substitute F (C a⁻¹) = C a⁻¹ by simp [substitute], hPF]
      change C a⁻¹ * (C a * X k + P - P) = X k
      rw [add_sub_cancel_right, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha,
        map_one, one_mul]
    · simp [substitute_X, hi]

/-- A triangular polynomial map with nonzero diagonal coefficients has a
polynomial two-sided inverse.  Each lower term in coordinate `i` involves
only the variables with indices strictly below `i`. -/
theorem triangular_twoSidedInverse (n : ℕ)
    (a : Fin n → K) (ha : ∀ i, a i ≠ 0)
    (p : ∀ i : Fin n, MvPolynomial (Fin i.val) K) :
    ∃ G : Fin n → MvPolynomial (Fin n) K,
      TwoSidedInverse
        (fun i => C (a i) * X i +
          rename (Fin.castLE (Nat.le_of_lt i.isLt)) (p i)) G := by
  induction n with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      constructor <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
      let a₀ : Fin n → K := fun i => a i.castSucc
      let p₀ : ∀ i : Fin n, MvPolynomial (Fin i.val) K := fun i => p i.castSucc
      obtain ⟨g₀, hg₀⟩ := ih a₀ (fun i => ha i.castSucc) p₀
      let f₀ : Fin n → MvPolynomial (Fin n) K := fun i =>
        C (a₀ i) * X i +
          rename (Fin.castLE (Nat.le_of_lt i.isLt)) (p₀ i)
      have hlift : TwoSidedInverse (finSuccLift f₀) (finSuccLift g₀) :=
        finSuccLift_twoSidedInverse hg₀
      let k : Fin (n + 1) := Fin.last n
      let e : Fin n → Fin (n + 1) := Fin.castSucc
      let E : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K := fun i =>
        if i = k then C (a k) * X k + rename e (p k) else X i
      let E' : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K := fun i =>
        if i = k then C (a k)⁻¹ * (X k - rename e (p k)) else X i
      have he : ∀ j : Fin n, e j ≠ k := by
        intro j h
        have := congrArg Fin.val h
        simp [e, k] at this
        omega
      have hE : TwoSidedInverse E E' := by
        exact elementaryTriangular_twoSidedInverse e k he (a k) (ha k) (p k)
      refine ⟨compose E' (finSuccLift g₀), ?_⟩
      have hcomp := twoSidedInverse_comp hlift hE
      have hmap :
          (fun i : Fin (n + 1) => C (a i) * X i +
            rename (Fin.castLE (Nat.le_of_lt i.isLt)) (p i)) =
            compose (finSuccLift f₀) E := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [compose, finSuccLift, E, e, k, substitute_X]
          apply congrArg (fun u => rename u (p (Fin.last n)))
          funext r
          apply Fin.ext
          rfl
        · change _ = substitute E (finSuccLift f₀ j.castSucc)
          rw [finSuccLift_castSucc]
          rw [substitute_rename_of_eq_on Fin.castSucc E]
          · simp [f₀, a₀, p₀]
            apply congrArg (fun u => rename u (p j.castSucc))
            funext r
            apply Fin.ext
            rfl
          · intro r
            simp [E, e, k, he r]
      rw [hmap]
      exact hcomp

end PolynomialMap
end HessianAlgebra
