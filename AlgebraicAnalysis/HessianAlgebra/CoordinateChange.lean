/- SPDX-License-Identifier: Apache-2.0 -/
-- Modified by itpplasma/algebraic-analysis: package module path changed.

import AlgebraicAnalysis.HessianAlgebra.AffineInverse
import Mathlib.Data.Matrix.Basic

/-! Polynomial substitution identities for invertible linear changes of source coordinates. -/

noncomputable section

namespace HessianAlgebra
namespace PolynomialMap

open MvPolynomial

variable {K : Type*} {σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

local notation "Poly" => MvPolynomial σ K

def compose (f g : σ → Poly) : σ → Poly :=
  fun i => substitute g (f i)

def linear (T : Matrix σ σ K) : σ → Poly := affine T 0

def transposeLinear (T : Matrix σ σ K) : σ → Poly := linear T.transpose

def identityMap : σ → Poly := X

lemma compose_identity_left (f : σ → Poly) : compose identityMap f = f := by
  funext i
  simp [compose, identityMap, substitute]

lemma compose_identity_right (f : σ → Poly) : compose f identityMap = f := by
  funext i
  simp [compose, identityMap, substitute]

lemma substitute_comp (g h : σ → Poly) (p : Poly) :
    substitute h (substitute g p) = substitute (compose g h) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [substitute]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp, substitute_X, compose]

lemma compose_assoc (f g h : σ → Poly) :
    compose (compose f g) h = compose f (compose g h) := by
  funext i
  exact substitute_comp g h (f i)

lemma partial_linear (T : Matrix σ σ K) (i j : σ) :
    partialDerivative j (linear T i) = C (T i j) := by
  unfold linear affine partialDerivative
  rw [map_add, map_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [pderiv_X_of_ne hkj]
  · simp

lemma gradient_linear_pullback (f : Poly) (T : Matrix σ σ K) :
    gradient (substitute (linear T) f) =
      fun j => ∑ i, substitute (linear T) (partialDerivative i f) * C (T i j) := by
  funext j
  calc
    pderiv j (substitute (linear T) f) =
        ∑ i, substitute (linear T) (partialDerivative i f) *
          partialDerivative j (linear T i) := pderiv_substitute f (linear T) j
    _ = ∑ i, substitute (linear T) (partialDerivative i f) * C (T i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [partial_linear]

lemma transpose_linear_comp_gradient_pullback (f : Poly) (T : Matrix σ σ K) :
    compose (linear T.transpose)
      (compose (gradient f) (linear T)) =
      gradient (substitute (linear T) f) := by
  funext j
  change substitute (compose (gradient f) (linear T))
      (∑ i, C (T i j) * X i + C 0) = _
  rw [gradient_linear_pullback]
  rw [map_add, map_sum]
  simp only [map_mul, map_C, map_X]
  simp [substitute, compose, gradient, linear, affine, Matrix.transpose_apply, mul_comm]

lemma twoSidedInverse_comp {f g f' g' : σ → Poly}
    (hf : TwoSidedInverse f f') (hg : TwoSidedInverse g g') :
    TwoSidedInverse (compose f g) (compose g' f') := by
  constructor
  · intro i
    change substitute (compose g' f') (substitute g (f i)) = X i
    rw [← substitute_comp]
    rw [substitute_comp g g']
    have hgg : compose g g' = X := by
      funext k
      exact hg.compose_forward k
    rw [hgg]
    simpa [substitute] using hf.compose_forward i
  · intro i
    change substitute (compose f g) (substitute f' (g' i)) = X i
    rw [← substitute_comp]
    rw [substitute_comp f' f]
    have hff : compose f' f = X := by
      funext k
      exact hf.compose_reverse k
    rw [hff]
    simpa [substitute] using hg.compose_reverse i

lemma conjugate_map_eq {f g l l' r r' : σ → Poly}
    (hl : TwoSidedInverse l l') (hr : TwoSidedInverse r r')
    (hg : g = compose l (compose f r)) :
    f = compose l' (compose g r') := by
  have hll : compose l' l = identityMap := by
    funext i
    exact hl.compose_reverse i
  have hrr : compose r r' = identityMap := by
    funext i
    exact hr.compose_forward i
  symm
  calc
    compose l' (compose g r') =
        compose l' (compose (compose l (compose f r)) r') := by rw [hg]
    _ = compose l' (compose l (compose (compose f r) r')) := by
      rw [compose_assoc]
    _ = compose l' (compose l (compose f (compose r r'))) := by
      rw [compose_assoc]
    _ = compose l' (compose l (compose f identityMap)) := by rw [hrr]
    _ = compose l' (compose l f) := by rw [compose_identity_right]
    _ = compose (compose l' l) f := by rw [compose_assoc]
    _ = compose identityMap f := by rw [hll]
    _ = f := compose_identity_left f

lemma gradient_inverse_under_linear_change
    (f : Poly) (T : Matrix σ σ K) (H : σ → Poly) (hdet : T.det ≠ 0)
    (hH : TwoSidedInverse (gradient (substitute (linear T) f)) H) :
    TwoSidedInverse (gradient f)
      (compose (linear T) (compose H (linear T.transpose))) := by
  have hdetT : T.transpose.det ≠ 0 := by
    simpa [Matrix.det_transpose] using hdet
  let hL := affine_twoSidedInverse T 0 hdet
  let hLt := affine_twoSidedInverse T.transpose 0 hdetT
  have hG : gradient (substitute (linear T) f) =
      compose (linear T.transpose) (compose (gradient f) (linear T)) :=
    (transpose_linear_comp_gradient_pullback f T).symm
  have hconj : gradient f =
      compose (affineInverse T.transpose 0)
        (compose (gradient (substitute (linear T) f)) (affineInverse T 0)) := by
    apply conjugate_map_eq (f := gradient f)
      (g := gradient (substitute (linear T) f))
      (l := linear T.transpose) (l' := affineInverse T.transpose 0)
      (r := linear T) (r' := affineInverse T 0)
      hLt hL hG
  have hinner : TwoSidedInverse
    (compose (gradient (substitute (linear T) f)) (affineInverse T 0))
      (compose (linear T) H) :=
    twoSidedInverse_comp hH ⟨hL.compose_reverse, hL.compose_forward⟩
  have houter : TwoSidedInverse
      (compose (affineInverse T.transpose 0)
        (compose (gradient (substitute (linear T) f)) (affineInverse T 0)))
      (compose (compose (linear T) H) (linear T.transpose)) := by
    apply twoSidedInverse_comp
    · exact ⟨hLt.compose_reverse, hLt.compose_forward⟩
    · exact hinner
  rw [hconj]
  simpa [compose_assoc] using houter

end PolynomialMap
end HessianAlgebra

end
