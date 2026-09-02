import AlgebraicAnalysis

/-! Small API consumer for the first extracted Ore slice. -/

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreActiveCoordinate
open AlgebraicAnalysis.OreActiveCoordinate.ActiveCoordinateData
open AlgebraicAnalysis.OreLeftPBW
open AlgebraicAnalysis.OreRightPBW
open AlgebraicAnalysis.OreRightIntersection
open AlgebraicAnalysis.OrePrincipalRightIdeal
open AlgebraicAnalysis.OreTower
open AlgebraicAnalysis.OreIteratedTower
open AlgebraicAnalysis.OreIteratedPBW
open AlgebraicAnalysis.OreStageLocalization
open AlgebraicAnalysis.OreLocalizationExtension
open AlgebraicAnalysis.RankTorsion
open AlgebraicAnalysis.StablyFree
open AlgebraicAnalysis.RankExact
open AlgebraicAnalysis.DenominatorTorsion
open AlgebraicAnalysis.TriangularDenominator
open AlgebraicAnalysis.Unimodular
open AlgebraicAnalysis.FreeSummandInduction
open AlgebraicAnalysis.TorsionProjectiveImage
open AlgebraicAnalysis.FilteredSchreyer
open AlgebraicAnalysis.InverseEulerRiccati
open AlgebraicAnalysis.NoncommutativeDerivation
open AlgebraicAnalysis.Splice
open AlgebraicAnalysis.TwoSimplicity
open AlgebraicAnalysis.Escape
open AlgebraicAnalysis.EscapeSpan
open AlgebraicAnalysis.EscapeAssembly
open AlgebraicAnalysis.RightCoordinates
open OreLocalization
open MulOpposite

noncomputable section

example {A : Type*} [Ring A] (u v x : A) :
    AlgebraicAnalysis.ringCommutator (u * v) x =
      u * AlgebraicAnalysis.ringCommutator v x +
        AlgebraicAnalysis.ringCommutator u x * v := by
  exact AlgebraicAnalysis.ringCommutator_mul u v x

example {A : Type*} [Ring A] (z x : A)
    (h : AlgebraicAnalysis.ringCommutator z x = 1) :
    AlgebraicAnalysis.ringCommutator (z ^ 3) x = 3 • z ^ 2 := by
  simpa using AlgebraicAnalysis.ringCommutator_pow z x h 3

def zeroDerivation : OreDivisionDerivation ℚ where
  toFun := fun _ => 0
  map_zero' := by simp
  map_add' := by intro a b; simp
  leibniz' := by intro a b; simp

def polynomialDerivation : OreDivisionDerivation (Polynomial ℚ) where
  toFun := Polynomial.derivative
  map_zero' := Polynomial.derivative_zero
  map_add' := by intro p q; exact Polynomial.derivative_add
  leibniz' := by intro p q; simpa [add_comm] using (Polynomial.derivative_mul (f := p) (g := q))

def polynomialActiveCoordinate :
    ActiveCoordinateData ℚ (Polynomial ℚ) where
  derivation := polynomialDerivation
  coordinate := Polynomial.X
  coordinate_central := by
    intro p
    exact (commute_iff_eq _ _).2 (mul_comm _ _)
  derivation_smul := by
    intro a
    simp [polynomialDerivation]
  derivation_coordinate := by
    simp [polynomialDerivation]

example :
    activeVariable polynomialActiveCoordinate *
        coefficient polynomialActiveCoordinate Polynomial.X =
      coefficient polynomialActiveCoordinate Polynomial.X *
          activeVariable polynomialActiveCoordinate +
        coefficient polynomialActiveCoordinate (algebraMap ℚ (Polynomial ℚ) 1) := by
  exact ActiveCoordinateData.variable_mul_coordinate polynomialActiveCoordinate

example (d : polynomialActiveCoordinate.Ore) :
    ∃ p : Polynomial (Polynomial ℚ),
      d = ∑ j ∈ p.support,
        coefficient polynomialActiveCoordinate (p.coeff j) *
            activeVariable polynomialActiveCoordinate ^ j ∧
      ∀ n : ℕ, ∀ q : Polynomial ℚ,
        Commute (coefficient polynomialActiveCoordinate (p.coeff n))
          (coordinatePolynomial polynomialActiveCoordinate q) := by
  exact ActiveCoordinateData.exists_active_expansion polynomialActiveCoordinate d

example (p q r : Polynomial ℚ) :
    rightMul zeroDerivation (rightMul zeroDerivation p q) r =
      rightMul zeroDerivation p (rightMul zeroDerivation q r) := by
  exact rightMul_assoc_of_ring zeroDerivation p q r

example (D : OreDivisionDerivation ℚ) (n : ℕ) :
    orePBWBasis D n = normalVariable D ^ n := by
  exact orePBWBasis_apply D n

example (D : OreDivisionDerivation ℚ) (n : ℕ) :
    rightOrePBWBasis D n = rightPBWMonomial D n := by
  exact rightOrePBWBasis_apply D n

example (Ds : List (Derivation ℚ)) (hDs : PairwiseCommutes Ds) :
    Function.Injective (iteratedNormalForm Ds hDs) := by
  exact iteratedNormalForm_injective Ds hDs

example (Ds : List (KDerivation ℚ)) (hDs : PairwiseCommutes Ds) :
    Basis (exponentIndex Ds) ℚ (OreTower Ds hDs) := by
  exact towerPBWBasis Ds hDs

example : RightOreCondition ℤ := by
  intro a b ha hb
  refine ⟨b, a, ?_, mul_ne_zero ha hb⟩
  simp [mul_comm]

example : ∃ x : ℤ, x ≠ 0 ∧
    ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      x ∈ (fun _ : Fin 2 ↦ (⊤ : Submodule (ℤᵐᵒᵖ) ℤ)) i := by
  apply exists_mem_finset_rightIdeals
    (s := (Finset.univ : Finset (Fin 2)))
    (I := fun _ : Fin 2 ↦ (⊤ : Submodule (ℤᵐᵒᵖ) ℤ))
  · intro i hi
    exact ⟨1, Submodule.mem_top, one_ne_zero⟩
  · exact (by
      intro a b ha hb
      refine ⟨b, a, ?_, mul_ne_zero ha hb⟩
      simp [mul_comm])

example (a : NormalOre zeroDerivation) :
    ∃ q r : Polynomial ℚ,
      a = normalForm zeroDerivation
          (rightMul zeroDerivation (Polynomial.X : Polynomial ℚ) q) +
            normalForm zeroDerivation r ∧
        (r = 0 ∨ r.natDegree < (Polynomial.X : Polynomial ℚ).natDegree) := by
  exact normalOre_right_division zeroDerivation (Polynomial.X : Polynomial ℚ)
    Polynomial.monic_X a

example (I : Submodule (NormalOre zeroDerivation)ᵐᵒᵖ (NormalOre zeroDerivation)) :
    ∃ a : NormalOre zeroDerivation,
      I = normalOrePrincipalRightIdealElement zeroDerivation a := by
  exact rightIdeal_isPrincipal zeroDerivation I

example {Q V W : Type} [DivisionRing Q]
    [AddCommGroup V] [Module Q V] [AddCommGroup W] [Module Q W] :
    Module.rank Q (V × W) = Module.rank Q V + Module.rank Q W := by
  exact rank_prod_add

example {R : Type*} [Ring R] [Nontrivial R] [NoZeroDivisors R]
    {S : Submonoid R} [OreSet S] (s : Finset S) :
    ∃ t : S, ∀ a ∈ s, ∃ u : R, (t : R) = u * (a : R) := by
  exact exists_common_left_multiple s

example {R M : Type*} [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]
    (N : Submodule Rᵐᵒᵖ M)
    (hclear : HasDenominatorClearance (R := R) N) :
    DenominatorTorsion.IsTorsionRight (R := R) (M := M ⧸ N) := by
  exact quotient_isTorsion_of_clearance N hclear

example {R : Type*} [Ring R] [IsDomain R] {M : Type*}
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    (F : ℕ → Submodule Rᵐᵒᵖ M) (n : ℕ)
    (hstep : ∀ i < n, StepClearance F i) {m : M} (hm : m ∈ F n) :
    ∃ s : R, s ≠ 0 ∧ (op s) • m ∈ F 0 := by
  exact filtration_clearance F n hstep hm

universe u

example {R : Type u} [Ring R] (P : Type u)
    [AddCommGroup P] [Module Rᵐᵒᵖ P]
    (h : StablyFreeProjectives R)
    (hP : Module.Projective Rᵐᵒᵖ P) (hfin : Module.Finite Rᵐᵒᵖ P) :
    ∃ m n : ℕ,
      Nonempty (P × (Fin m → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)) :=
  h P hP hfin

example {B : Type*} [Ring B] (D : OreDivisionDerivation B)
    (S : Submonoid B) [OreSet S]
    [OreSet (S.map (normalCoefficient D).toMonoidHom)]
    (L : IsDerivationOreLocalization D S) :
    ∃ (D' : OreDivisionDerivation (B[S⁻¹]))
      (e : (NormalOre D)[(S.map (normalCoefficient D).toMonoidHom)⁻¹] ≃+*
        NormalOre D'),
      ∀ b : B,
        e (numeratorHom (normalCoefficient D b)) =
          normalCoefficient D' (numeratorHom b) :=
  L

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] {x : R}
    (hx : Function.Surjective fun m : M ↦ x • m) :
    Disjoint (Module.support R M)
      (PrimeSpectrum.zeroLocus ({x} : Set R)) :=
  AlgebraicAnalysis.HyperplaneRestriction.support_disjoint_zeroLocus_of_smul_surjective
    hx

example : AlgebraicAnalysis.Unimodular.IsUnimodular (R := ℤ) (N := ℤ) 1 := by
  refine ⟨LinearMap.id, ?_⟩
  rfl

example : ∃ φ : ℤ →ₗ[ℤ] ℤ, Function.Surjective φ := by
  apply (AlgebraicAnalysis.Unimodular.exists_unimodular_iff_surjective
    (R := ℤ) (N := ℤ)).mp
  exact ⟨1, LinearMap.id, rfl⟩

example : ∃ q₁ : ℤ →ₗ[ℤ] ℤ, Function.Surjective q₁ := by
  let q : ℤ × ℤ →ₗ[ℤ] ℤ := LinearMap.fst ℤ ℤ ℤ
  have hkill : ∀ z : ℤ, q (0, z) = 0 := by
    intro z
    rfl
  apply AlgebraicAnalysis.TorsionProjectiveImage.surjective_factor_first_of_surjective
    q hkill
  intro z
  exact ⟨(z, 0), rfl⟩

example {A : Type*} [Ring A] (p z : A) :
    AlgebraicAnalysis.InverseEulerRiccati.adIterate p 0 z = z := by
  rfl

example {A : Type*} [Ring A] (p z : A) :
    AlgebraicAnalysis.InverseEulerRiccati.adIterate p 1 z =
      AlgebraicAnalysis.ringCommutator p z := by
  rfl

example {A : Type*} {E : Type*} [Ring A] [AddCommGroup E]
    [Module Aᵐᵒᵖ E]
    (phi : E →ₗ[Aᵐᵒᵖ] A) (L : AddSubgroup A)
    (a : E) (C x : A)
    (ha : phi a = 1 + C * x) (hone : (1 : A) ∈ L)
    (hLx : ∀ z : A, z ∈ L → z * x ∈ L)
    (hstrict : ∀ z : A, z * x ∈ L → z ∈ L) :
    (∃ b : E, ∃ l : A, l ∈ L ∧ C = phi b + l) ↔
      ∃ t b : E, phi t ∈ L ∧
        a = t + (MulOpposite.op x) • b :=
  range_add_lower_iff_preimage_add_rightMultiple
    phi L a C x ha hone hLx hstrict

example {E : Type*} [Ring E] [Nontrivial E]
    (d : E →+ E) (hd : IsDerivation d) (x : E)
    (hx : ∀ y : E, Commute x y) (hdx : d x = 1) :
    ¬ IsInnerDerivation d := by
  exact not_inner_of_central_coordinate d hd x hx hdx

example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N N' U : Submodule R M}
    (hNU : N ≤ U) (hNN' : N ⋖ N')
    (hsup : N' ⊔ U = ⊤) (hUtop : U ≠ ⊤) :
    IsCoatom U := by
  exact isCoatom_of_covBy_sup_eq_top hNU hNN' hsup hUtop

example {Λ Γ : Type*} [Ring Λ] [Ring Γ]
    (ι : Λ →+* Γ) (hΛ : TwoSimple Λ)
    (hquot : PrincipalRightQuotientTorsion ι) :
    TwoSimple Γ := by
  exact twoSimple_of_principalRightQuotientTorsion ι hΛ hquot

example {S ι : Type*} [Ring S] (v : ι →₀ S) (a b : S) :
    rightCoordinateAction (rightCoordinateAction v a) b =
      rightCoordinateAction v (a * b) := by
  exact rightCoordinateAction_mul v a b

example {S : Type*} [Ring S] {n : ℕ}
    (H : Submodule Sᵐᵒᵖ (Fin n → S))
    (hunit : ∀ i : Fin n, ∃ u : S, IsUnit u ∧
      (Pi.single i u : Fin n → S) ∈ H) :
    H = ⊤ := by
  exact top_of_unit_singletons H hunit

example {E S : Type*} [DivisionRing E] [CharZero E] [Ring S]
    {n : ℕ} (D : CentralEscapeData (E := E) (S := S))
    (p : Fin n → Polynomial E) (hp : ∀ i, p i ≠ 0)
    (hstrict : StrictAnti (fun i => (p i).natDegree))
    (H : Submodule Sᵐᵒᵖ (Fin n → S))
    (hv : (fun i => D.normal (p i)) ∈ H)
    (hleft : ∀ v : Fin n → S, v ∈ H →
      (fun i => D.embed D.coordinate * v i) ∈ H) :
    H = ⊤ := by
  exact finite_tuple_escape D p hp hstrict H hv hleft

end
