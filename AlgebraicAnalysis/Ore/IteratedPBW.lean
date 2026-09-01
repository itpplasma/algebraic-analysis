import AlgebraicAnalysis.Ore.IteratedTower

/-!
# Left-field PBW bases for the finite Ore tower

This is the noncentral left-module layer.  Scalars act through the canonical
coefficient embedding at every stage; no centrality of the coefficient field
inside the Ore ring is used.
-/

namespace AlgebraicAnalysis.OreIteratedPBW

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreIteratedTower

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

abbrev KDerivation (K : Type*) [Ring K] := OreDivisionDerivation K

def towerCoefficient : (Ds : List (KDerivation K)) →
    (hDs : PairwiseCommutes Ds) → K →+* OreTower Ds hDs
  | [], _ => RingHom.id K
  | D :: Ds, hDs =>
      let T := build Ds hDs.2
      let hD : CommutesWith D Ds := pairwise_head hDs
      (normalCoefficient (T.extend D hD)).comp
        (towerCoefficient Ds hDs.2)

instance towerKModule (Ds : List (KDerivation K))
    (hDs : PairwiseCommutes Ds) : Module K (OreTower Ds hDs) :=
  Module.compHom (OreTower Ds hDs) (towerCoefficient Ds hDs)

def exponentIndex : List (KDerivation K) → Type
  | [] => PUnit
  | _ :: Ds => ℕ × exponentIndex Ds

instance polynomialKSMul (R : Type*) [Semiring R] [Module K R] :
    SMul K (Polynomial R) :=
  ⟨fun c p => (Polynomial.toFinsuppIso R).symm (c •
      (Polynomial.toFinsuppIso R) p)⟩

instance polynomialKModule (R : Type*) [Semiring R] [Module K R] :
    Module K (Polynomial R) where
  one_smul p := by
    apply (Polynomial.toFinsuppIso R).injective
    simp [polynomialKSMul]
  mul_smul c d p := by
    apply (Polynomial.toFinsuppIso R).injective
    simp [polynomialKSMul, mul_smul]
  smul_zero c := by
    apply (Polynomial.toFinsuppIso R).injective
    simp [polynomialKSMul]
  smul_add c p q := by
    apply (Polynomial.toFinsuppIso R).injective
    simp [polynomialKSMul]
  add_smul c d p := by
    apply (Polynomial.toFinsuppIso R).injective
    ext n
    simp only [polynomialKSMul, AddEquiv.apply_symm_apply, Finsupp.add_apply,
      add_smul]
  zero_smul p := by
    apply (Polynomial.toFinsuppIso R).injective
    simp [polynomialKSMul]

lemma polynomial_smul_eq_C_mul {R : Type*} [Ring R] [Module K R]
    (φ : K →+* R) (hφ : ∀ c : K, ∀ r : R, c • r = φ c * r)
    (c : K) (p : Polynomial R) :
    c • p = Polynomial.C (φ c) * p := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
      rw [smul_add, mul_add, hp, hq]
  | h_monomial n r =>
      apply (Polynomial.toFinsuppIso R).injective
      simp [polynomialKSMul, Polynomial.toFinsuppIso, hφ]

def polynomialToFinsuppLinearEquiv {R : Type*} [Ring R]
    [Module K R] :
    Polynomial R ≃ₗ[K] (ℕ →₀ R) := by
  exact
    { (Polynomial.toFinsuppIso R).toAddEquiv with
      map_smul' := by
        intro c p
        ext n
        rfl }

def polynomialBasis (R : Type*) [Ring R] [Module K R]
    (b : Basis ι K R) :
    Basis (ℕ × ι) K (Polynomial R) := by
  let e : Polynomial R ≃ₗ[K] (ℕ × ι →₀ K) :=
    (polynomialToFinsuppLinearEquiv (K := K)).trans
      ((Finsupp.mapRange.linearEquiv b.repr).trans
        (Finsupp.finsuppProdLEquiv K).symm)
  exact Basis.ofRepr e

def normalFormLinearEquivK {R : Type*} [Ring R]
    (D : OreDivisionDerivation R) (φ : K →+* R)
    (ψ : K →+* NormalOre D)
    (hψ : ψ = (normalCoefficient D).comp φ)
    [Module K R] [Module K (NormalOre D)]
    (hφ : ∀ c : K, ∀ r : R, c • r = φ c * r)
    (hsmul : ∀ c : K, ∀ z : NormalOre D, c • z = ψ c * z) :
    Polynomial R ≃ₗ[K] NormalOre D := by
  exact
    { normalFormAddEquiv D with
      map_smul' := by
        intro c p
        change normalForm D (c • p) = c • normalForm D p
        rw [polynomial_smul_eq_C_mul φ hφ]
        rw [hsmul, hψ]
        induction p using Polynomial.induction_on' with
        | h_add p q hp hq =>
            rw [mul_add, normalForm_add, hp, hq, normalForm_add]
            noncomm_ring
        | h_monomial n b =>
            rw [Polynomial.C_mul_monomial, normalForm_monomial]
            rw [normalForm_monomial]
            simp [hψ, mul_assoc] }

def towerPBWBasis : (Ds : List (KDerivation K)) →
    (hDs : PairwiseCommutes Ds) →
    letI : Module K (OreTower Ds hDs) := towerKModule Ds hDs
    Basis (exponentIndex Ds) K (OreTower Ds hDs)
  | [], _ => Basis.singleton PUnit K
  | D :: Ds, hDs => by
      letI : Module K (OreTower (D :: Ds) hDs) :=
        towerKModule (D :: Ds) hDs
      let T := build Ds hDs.2
      let hD : CommutesWith D Ds := pairwise_head hDs
      let φ : K →+* T.carrier := towerCoefficient Ds hDs.2
      let ψ : K →+* NormalOre (T.extend D hD) :=
        (normalCoefficient (T.extend D hD)).comp φ
      letI : Module K T.carrier := towerKModule Ds hDs.2
      letI : Module K (NormalOre (T.extend D hD)) :=
        towerKModule (D :: Ds) hDs
      let b : Basis (exponentIndex Ds) K T.carrier :=
        towerPBWBasis Ds hDs.2
      let pb : Basis (ℕ × exponentIndex Ds) K (Polynomial T.carrier) :=
        polynomialBasis (K := K) T.carrier b
      exact (pb.map (normalFormLinearEquivK (K := K)
        (T.extend D hD) φ ψ rfl (by intro c r; rfl) (by intro c z; rfl)))

#print axioms towerCoefficient
#print axioms polynomialBasis
#print axioms normalFormLinearEquivK
#print axioms towerPBWBasis

end
end AlgebraicAnalysis.OreIteratedPBW
