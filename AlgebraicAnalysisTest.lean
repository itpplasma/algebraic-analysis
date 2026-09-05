import AlgebraicAnalysis
import AlgebraicAnalysisTest.TwoGeneratorIdentity
import AlgebraicAnalysisTest.DifferentialOperatorsBasic

/-! Small API consumer for the first extracted Ore slice. -/

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreActiveCoordinate
open AlgebraicAnalysis.OreActiveCoordinate.ActiveCoordinateData
open AlgebraicAnalysis.OreLeftPBW
open AlgebraicAnalysis.OreRightPBW
open AlgebraicAnalysis.OreRightQuotient
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
open AlgebraicAnalysis.FunctionField
open OreLocalization
open MulOpposite

noncomputable section

/-- Concrete function-field consumer: the rational function field is finitely
generated as a field extension, although not as a polynomial algebra. -/
example :
    (⊤ : IntermediateField ℚ (FractionRing (Polynomial ℚ))).FG := by
  exact top_fg_of_finiteType_fractionRing
    ℚ (Polynomial ℚ) (FractionRing (Polynomial ℚ))

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

def matrixZeroDerivation :
    OreDivisionDerivation (Matrix (Fin 2) (Fin 2) ℚ) where
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

def quadraticOrePolynomial : Polynomial ℚ := Polynomial.X ^ 2 + 1

theorem quadraticOrePolynomial_monic : quadraticOrePolynomial.Monic := by
  exact Polynomial.Monic.add_of_left (Polynomial.monic_X_pow 2)
    (by simp [quadraticOrePolynomial])

/-- Concrete rank-two consumer of monic principal-quotient freeness. -/
example : Module.Basis (Fin 2) ℚᵐᵒᵖ
    (TwoGeneratorQuotient zeroDerivation quadraticOrePolynomial 0) := by
  simpa [quadraticOrePolynomial,
    Polynomial.natDegree_add_eq_left_of_degree_lt
      (show (1 : Polynomial ℚ).degree <
          (Polynomial.X ^ 2 : Polynomial ℚ).degree by simp)] using
    monicPrincipalRightQuotientBasis zeroDerivation quadraticOrePolynomial
      quadraticOrePolynomial_monic

/-- Independent quotient oracle: in the same concrete quotient, `X² = -1`. -/
example :
    Submodule.Quotient.mk
        (p := twoGeneratorCoeffSubmodule zeroDerivation quadraticOrePolynomial 0)
        (normalForm zeroDerivation (Polynomial.X ^ 2)) =
      -Submodule.Quotient.mk
        (p := twoGeneratorCoeffSubmodule zeroDerivation quadraticOrePolynomial 0)
        (normalForm zeroDerivation 1) := by
  have hmem : normalForm zeroDerivation quadraticOrePolynomial ∈
      twoGeneratorCoeffSubmodule zeroDerivation quadraticOrePolynomial 0 := by
    change normalForm zeroDerivation quadraticOrePolynomial ∈
      twoGeneratorRightIdeal zeroDerivation quadraticOrePolynomial 0
    exact normalForm_H_mem_twoGeneratorRightIdeal
      zeroDerivation quadraticOrePolynomial 0
  have hzero :
      Submodule.Quotient.mk
          (p := twoGeneratorCoeffSubmodule zeroDerivation quadraticOrePolynomial 0)
          (normalForm zeroDerivation quadraticOrePolynomial) = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (twoGeneratorCoeffSubmodule zeroDerivation quadraticOrePolynomial 0)).2 hmem
  rw [quadraticOrePolynomial, normalForm_add] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- Basis-sensitive noncommutative oracle: successive right coefficients are
recovered in their written product order inside the opposite-ring
coordinate. -/
example (a b : Matrix (Fin 2) (Fin 2) ℚ) :
    let H : Polynomial (Matrix (Fin 2) (Fin 2) ℚ) := Polynomial.X ^ 2 + 1
    let hH : H.Monic := Polynomial.Monic.add_of_left
      (Polynomial.monic_X_pow 2) (by simp [H])
    let j : Fin H.natDegree := ⟨1, by
      simpa [H, Polynomial.natDegree_add_eq_left_of_degree_lt
        (show (1 : Polynomial (Matrix (Fin 2) (Fin 2) ℚ)).degree <
          (Polynomial.X ^ 2).degree by simp)]⟩
    (monicPrincipalRightQuotientBasis matrixZeroDerivation H hH).repr
        (Submodule.Quotient.mk
          (normalForm matrixZeroDerivation
            (rightMul matrixZeroDerivation
              (rightMul matrixZeroDerivation Polynomial.X (Polynomial.C a))
              (Polynomial.C b)))) =
      Finsupp.single j (MulOpposite.op (a * b)) := by
  dsimp only
  let H : Polynomial (Matrix (Fin 2) (Fin 2) ℚ) := Polynomial.X ^ 2 + 1
  let hH : H.Monic := Polynomial.Monic.add_of_left
    (Polynomial.monic_X_pow 2) (by simp [H])
  let j : Fin H.natDegree := ⟨1, by
    simpa [H, Polynomial.natDegree_add_eq_left_of_degree_lt
      (show (1 : Polynomial (Matrix (Fin 2) (Fin 2) ℚ)).degree <
        (Polynomial.X ^ 2).degree by simp)]⟩
  let β := monicPrincipalRightQuotientBasis matrixZeroDerivation H hH
  have hclass :
      Submodule.Quotient.mk
          (normalForm matrixZeroDerivation
            (rightMul matrixZeroDerivation
              (rightMul matrixZeroDerivation Polynomial.X (Polynomial.C a))
              (Polynomial.C b))) =
        MulOpposite.op (a * b) • β j := by
    rw [normalForm_mul, normalForm_mul, normalForm_C, normalForm_C]
    have hbj : β j = Submodule.Quotient.mk
        (normalForm matrixZeroDerivation Polynomial.X) := by
      simpa [β, j] using
        (monicPrincipalRightQuotientBasis_apply matrixZeroDerivation H hH j)
    rw [hbj]
    change Submodule.Quotient.mk
        (normalForm matrixZeroDerivation Polynomial.X *
          normalCoefficient matrixZeroDerivation a *
          normalCoefficient matrixZeroDerivation b) =
      Submodule.Quotient.mk
        (MulOpposite.op (a * b) • normalForm matrixZeroDerivation Polynomial.X)
    rw [normalOre_op_smul_def, MulOpposite.unop_op,
      map_mul, mul_assoc]
  calc
    β.repr (Submodule.Quotient.mk
        (normalForm matrixZeroDerivation
          (rightMul matrixZeroDerivation
            (rightMul matrixZeroDerivation Polynomial.X (Polynomial.C a))
            (Polynomial.C b)))) =
        β.repr (MulOpposite.op (a * b) • β j) := congrArg β.repr hclass
    _ = MulOpposite.op (a * b) • β.repr (β j) := by rw [map_smul]
    _ = MulOpposite.op (a * b) • Finsupp.single j 1 := by rw [β.repr_self]
    _ = Finsupp.single j (MulOpposite.op (a * b)) := by
      rw [Finsupp.smul_single]
      simp

/-- The preceding product order is observable in the chosen coefficient
ring: these two explicit matrices do not commute. -/
example :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![0, 0; 1, 0] ≠
      !![0, 0; 1, 0] * !![0, 1; 0, 0] := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  norm_num [Matrix.mul_apply] at h00

example (Ds : List (Derivation ℚ)) (hDs : PairwiseCommutes Ds) :
    Function.Injective (iteratedNormalForm Ds hDs) := by
  exact iteratedNormalForm_injective Ds hDs

example (Ds : List (KDerivation ℚ)) (hDs : PairwiseCommutes Ds) :
    Module.Basis (exponentIndex Ds) ℚ (OreTower Ds hDs) := by
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

example :
    let P : MvPolynomial (Fin 2) ℚ :=
      MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2
    P - MvPolynomial.monomial (Finsupp.single 0 2) 1 ∈
      Ideal.span (MvPolynomial.X '' ({1} : Set (Fin 2))) := by
  dsimp
  apply AlgebraicAnalysis.MvPolynomial.sub_pureMonomial_mem_span_X
  · simpa using ((MvPolynomial.isHomogeneous_X ℚ (0 : Fin 2)).pow 2).add
      ((MvPolynomial.isHomogeneous_X ℚ (1 : Fin 2)).pow 2)
  · intro i hi
    have hi' := MvPolynomial.vars_add_subset
      (MvPolynomial.X (0 : Fin 2) ^ 2 : MvPolynomial (Fin 2) ℚ)
      (MvPolynomial.X (1 : Fin 2) ^ 2) hi
    rw [Finset.mem_union] at hi'
    rcases hi' with hi0 | hi1
    · left
      have := MvPolynomial.vars_pow
        (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℚ) 2 hi0
      simpa using this
    · right
      have := MvPolynomial.vars_pow
        (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ) 2 hi1
      simpa using this
  · have hne : Finsupp.single (1 : Fin 2) 2 ≠ Finsupp.single 0 2 := by
      intro h
      have h' := congrArg (fun f => f (1 : Fin 2)) h
      norm_num at h'
    simp [MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, hne]

example :
    let F : ℕ → Submodule ℚ ℚ := fun n ↦ if n = 0 then ⊥ else ⊤
    let neg : ℚ →ₗ[ℚ] ℚ := -LinearMap.id
    ∃ hF : Monotone F,
      ∃ hpres : ∀ n, ∀ x ∈ F n, neg x ∈ F n,
        Function.Surjective
          (AlgebraicAnalysis.FilteredStrictness.gradedQuotientMap
            F hF neg hpres 0 1 (by omega)) := by
  dsimp only
  let F : ℕ → Submodule ℚ ℚ := fun n ↦ if n = 0 then ⊥ else ⊤
  let neg : ℚ →ₗ[ℚ] ℚ := -LinearMap.id
  have hF : Monotone F := by
    intro m n hmn
    by_cases hm : m = 0
    · subst m
      simp [F]
    · have hn : n ≠ 0 := by omega
      simp [F, hm, hn]
  have hneg : Function.Surjective neg := by
    intro y
    exact ⟨-y, by simp [neg]⟩
  have hpres : ∀ n, ∀ x ∈ F n, neg x ∈ F n := by
    intro n x hx
    by_cases hn : n = 0
    · simp [F, hn] at hx ⊢
      simp [hx, neg]
    · simp [F, hn]
  have hstrict : AlgebraicAnalysis.FilteredStrictness.IsStrict F neg := by
    intro n
    have hrange : LinearMap.range neg = ⊤ :=
      LinearMap.range_eq_top.mpr hneg
    by_cases hn : n = 0 <;> simp [F, hn, hrange]
  exact ⟨hF, hpres,
    AlgebraicAnalysis.FilteredStrictness.gradedQuotientMap_surjective
      F hF neg hpres hstrict hneg 0 1 (by omega)⟩

/-- Behavioral check: on the nonzero graded piece of the two-step filtration,
the induced map is genuinely negation, not merely a map with the expected
type. -/
example :
    let F : ℕ → Submodule ℚ ℚ := fun n ↦ if n = 0 then ⊥ else ⊤
    let neg : ℚ →ₗ[ℚ] ℚ := -LinearMap.id
    let hF : Monotone F := by
      intro m n hmn
      by_cases hm : m = 0
      · subst m
        simp [F]
      · have hn : n ≠ 0 := by omega
        simp [F, hm, hn]
    let hpres : ∀ n, ∀ x ∈ F n, neg x ∈ F n := by
      intro n x hx
      by_cases hn : n = 0
      · simp [F, hn] at hx ⊢
        simp [hx, neg]
      · simp [F, hn]
    AlgebraicAnalysis.FilteredStrictness.gradedQuotientMap
        F hF neg hpres 0 1 (by omega)
        (Submodule.Quotient.mk
          (⟨1, by simp [F]⟩ : F 1)) =
      Submodule.Quotient.mk (⟨-1, by simp [F]⟩ : F 1) := by
  rfl

end
