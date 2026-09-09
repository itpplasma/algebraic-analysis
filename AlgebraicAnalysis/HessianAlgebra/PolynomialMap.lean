/- SPDX-License-Identifier: Apache-2.0 -/
-- Modified by itpplasma/algebraic-analysis: package module path changed.

import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
Calculus for polynomial self maps.  The coefficient field and the finite set
of variables are parameters, so the results can be reused by the four
variable development without baking that specialization into the API.
-/

noncomputable section

namespace HessianAlgebra
namespace PolynomialMap

open MvPolynomial

variable {R : Type*} {σ : Type*} [Field R] [Fintype σ] [DecidableEq σ]

local notation "Poly" => MvPolynomial σ R

def substitute (g : σ → Poly) : Poly →+* Poly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* Poly) g

def partialDerivative (i : σ) : Poly → Poly := fun f => MvPolynomial.pderiv i f

def gradient (f : Poly) : σ → Poly := fun i => partialDerivative i f

structure TwoSidedInverse (f g : σ → Poly) : Prop where
  compose_forward : ∀ i, substitute g (f i) = MvPolynomial.X i
  compose_reverse : ∀ i, substitute f (g i) = MvPolynomial.X i

def gradientTwoSidedInverse (f : Poly) (g : σ → Poly) : Prop :=
  TwoSidedInverse (gradient f) g

def legendrePolynomial (f : Poly) (g : σ → Poly) : Poly :=
  (Finset.univ.sum fun i => MvPolynomial.X i * g i) - substitute g f

def hessian (f : Poly) : σ → σ → Poly :=
  fun i j => partialDerivative i (partialDerivative j f)

lemma substitute_X (g : σ → Poly) (i : σ) :
    substitute g (X i) = g i := by
  simp [substitute]

lemma pderiv_substitute (f : Poly) (g : σ → Poly) (i : σ) :
    partialDerivative i (substitute g f) =
      ∑ j, substitute g (partialDerivative j f) * partialDerivative i (g j) := by
  change pderiv i (substitute g f) = ∑ j, substitute g (pderiv j f) * pderiv i (g j)
  induction f using MvPolynomial.induction_on with
  | C a => simp [substitute]
  | add p q hp hq =>
      simpa only [map_add, add_mul, Finset.sum_add_distrib] using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
      simp only [map_mul, pderiv_mul, map_add, add_mul, Finset.sum_add_distrib,
        substitute_X]
      rw [hp, Finset.sum_mul]
      apply congrArg₂ (fun a b : Poly => a + b)
      · apply Finset.sum_congr rfl
        intro j hj
        ring
      · symm
        rw [Finset.sum_eq_single k]
        · simp
        · intro j hj hne
          simp [pderiv_X_of_ne (Ne.symm hne)]
        · simp

lemma partial_comm (f : Poly) (i j : σ) :
    partialDerivative i (partialDerivative j f) =
      partialDerivative j (partialDerivative i f) := by
  classical
  ext d
  simp only [partialDerivative]
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv]
  by_cases hij : i = j
  · subst j
    simp [MvPolynomial.coeff_pderiv]
  · simp [MvPolynomial.coeff_pderiv, hij, Ne.symm hij, Finsupp.add_apply]
    rw [add_assoc, add_comm (Finsupp.single i 1) (Finsupp.single j 1), ← add_assoc]
    ring

lemma gradient_legendre (f : Poly) (g : σ → Poly)
    (hgi : gradientTwoSidedInverse f g) :
    gradient (legendrePolynomial f g) = g := by
  funext i
  change pderiv i (legendrePolynomial f g) = g i
  unfold legendrePolynomial
  rw [map_sub, map_sum]
  simp only [pderiv_mul, Finset.sum_add_distrib]
  have hfirst : (∑ j : σ, pderiv i (X j) * g j) = g i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hne
      simp [pderiv_X_of_ne hne]
    · simp
  rw [hfirst]
  have hc := pderiv_substitute f g i
  change pderiv i (substitute g f) = _ at hc
  rw [hc]
  have hf : ∀ j, substitute g (partialDerivative j f) = X j := hgi.compose_forward
  simp_rw [hf]
  change g i + (∑ j, X j * pderiv i (g j)) - (∑ j, X j * pderiv i (g j)) = g i
  exact add_sub_cancel_right _ _

end PolynomialMap
end HessianAlgebra

end
