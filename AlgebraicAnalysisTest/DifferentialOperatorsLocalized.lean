module
public import AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialOperators
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

/-!
Oracles for differential operators on localized polynomial rings and for the
principal symbol isomorphism.

Each oracle is an explicit computation, independent of the filtration and
presentation machinery.

* Laurent polynomials `ℚ[x, x⁻¹]`: the extended derivative satisfies
  `∂(x⁻¹) = -x⁻²`, derived by hand from `∂(x · x⁻¹) = 0`; the library value
  agrees. The operator `x⁻¹ ∂` (not a polynomial operator) has order one and
  not zero, by evaluation at `x`.
* Commutator test up to units: `[x⁻¹ ∂, x⁻¹]` is computed by evaluation to be
  multiplication by `-x⁻³`, an order-zero operator, as the test predicts from
  `[x⁻¹ ∂, x] = x⁻¹`.
* Simplicity and domain of `D_ℚ(ℚ[x, x⁻¹])` and `D_ℚ(ℚ(x₀, x₁))`, with
  `∂² (x⁻¹) = 2 x⁻³ ≠ 0` as an evaluation cross-check of `∂ · ∂ ≠ 0`.
* Injectivity of the symbol on `D_ℚ(ℚ[x])`: `∂²` does not have order one,
  by the library (`ξ²` is a nonzero homogeneous polynomial of degree two) and
  independently by the double commutator `[[∂², x], x] = 2`.
* Dimension: `dim ℚ[x, x⁻¹] ≤ 1` gives deviation at most `2`.
-/

namespace AlgebraicAnalysisTest.DifferentialOperatorsLocalized

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators MvPolynomial
open AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations
open AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialOperators

/-- The polynomial ring `ℚ[x]`. -/
abbrev P1 := MvPolynomial (Fin 1) ℚ

/-- The coordinate polynomial `x`. -/
noncomputable abbrev xP : P1 := X 0

/-- The Laurent polynomial ring `ℚ[x, x⁻¹]`. -/
abbrev L := Localization.Away xP

/-- The submonoid of powers of `x`. -/
noncomputable abbrev powersX : Submonoid P1 := Submonoid.powers xP

/-- `x` in `ℚ[x, x⁻¹]`. -/
noncomputable abbrev x : L := algebraMap P1 L xP

/-- `x⁻¹` in `ℚ[x, x⁻¹]`. -/
noncomputable abbrev xInv : L := IsLocalization.Away.invSelf xP

/-- The extended derivative `∂ = d/dx` on `ℚ[x, x⁻¹]`. -/
noncomputable abbrev dx : Derivation ℚ L L := localizedPderiv powersX L 0

theorem x_mul_xInv : x * xInv = 1 := IsLocalization.Away.mul_invSelf xP

theorem dx_x : dx x = 1 := by
  simpa using localizedPderiv_apply_algebraMap_X powersX L 0 0

/-- Hand computation: `∂(x⁻¹) = -x⁻²`, from `0 = ∂(x x⁻¹) = x ∂(x⁻¹) + x⁻¹`. -/
theorem dx_xInv : dx xInv = -(xInv * xInv) := by
  have h := dx.leibniz x xInv
  rw [x_mul_xInv, dx.map_one_eq_zero, dx_x, smul_eq_mul, smul_eq_mul, mul_one] at h
  calc dx xInv = xInv * (x * dx xInv) := by rw [← mul_assoc, mul_comm xInv x, x_mul_xInv, one_mul]
    _ = xInv * (-xInv) := by rw [show x * dx xInv = -xInv by linear_combination -h]
    _ = -(xInv * xInv) := by ring

theorem powersX_le : powersX ≤ nonZeroDivisors P1 :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0)

instance : IsDomain L := IsLocalization.isDomain_localization powersX_le

instance : CharZero L := algebraRat.charZero L

/-! ### The coordinate frame and the commutator test up to units -/

example : IsCoordinateFrame (coordinate (k := ℚ) (n := 1) L) (localizedPderiv powersX L) :=
  isCoordinateFrame powersX L

/-- The operator `x⁻¹ ∂`, which is not a polynomial differential operator. -/
noncomputable abbrev T : Module.End ℚ L := multiplication xInv * dx.toLinearMap

theorem T_mem_order_one : T ∈ order (k := ℚ) (R := L) 1 := by
  simpa using mul_mem_order (multiplication_mem_order_zero xInv) (derivation_mem_order_one dx)

/-- `x⁻¹ ∂` does not have order zero: `x⁻¹ ∂ (1) = 0` but `x⁻¹ ∂ (x) = x⁻¹ ≠ 0`. -/
example : T ∉ order (k := ℚ) (R := L) 0 := by
  intro h
  have h1 := LinearMap.congr_fun ((mem_order_zero_iff_eq_multiplication _).mp h) x
  simp only [T, Module.End.mul_apply, multiplication_apply, Derivation.coeFn_coe, dx_x,
    mul_one, dx.map_one_eq_zero, mul_zero, zero_mul] at h1
  have := congrArg (· * x) h1
  simp only [mul_comm xInv x, x_mul_xInv, zero_mul] at this
  exact one_ne_zero this

/-- Direct evaluation: `[x⁻¹ ∂, x⁻¹] = -x⁻³`, an order-zero operator. -/
theorem commutator_T_xInv :
    commutator T xInv = multiplication (-(xInv * xInv * xInv)) := by
  ext f
  simp only [T, commutator_apply, Module.End.mul_apply, multiplication_apply,
    Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, dx_xInv]
  ring

/-- The library commutator test up to units: `x⁻¹ ∂` has order at most one
because its commutator with the single coordinate `x` is multiplication by
`x⁻¹` (computed by evaluation), although `x` alone does not generate
`ℚ[x, x⁻¹]`. -/
example : T ∈ order (k := ℚ) (R := L) 1 := by
  refine (isCoordinateFrame powersX L).mem_order_iff.mpr fun i => ?_
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have hc : commutator T (coordinate (k := ℚ) (n := 1) L 0) = multiplication xInv := by
    ext f
    simp only [T, commutator_apply, Module.End.mul_apply, multiplication_apply,
      Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, coordinate]
    rw [show algebraMap P1 L (X 0) = x from rfl, dx_x]
    ring
  rw [hc, orderBelow_succ]
  exact multiplication_mem_order_zero _

/-- And the commutator with the inverse coordinate has order zero, by evaluation. -/
example : commutator T xInv ∈ order (k := ℚ) (R := L) 0 := by
  rw [commutator_T_xInv]
  exact multiplication_mem_order_zero _

/-! ### Noetherian, dimension, simplicity, domain, centre -/

example : ringKrullDim L ≤ 1 := by
  simpa using ringKrullDim_le powersX L

example : IsNoetherianRing (DiffOp ℚ L) := isNoetherianRing powersX L
example : IsNoetherian (DiffOp ℚ L)ᵐᵒᵖ (DiffOp ℚ L) := isNoetherian_right powersX L
example : Module.DevLE (DiffOp ℚ L)ᵐᵒᵖ 2 (DiffOp ℚ L) := devLE_right powersX L
example : Module.DevLE (DiffOp ℚ L) 2 (DiffOp ℚ L) := devLE_left powersX L
example : Module.DevLEOmega (DiffOp ℚ L)ᵐᵒᵖ (DiffOp ℚ L) := devLEOmega_right powersX L

/-- `∂` as an element of `D_ℚ(ℚ[x, x⁻¹])`. -/
noncomputable abbrev dxElem : DiffOp ℚ L := derivationElem dx

theorem dxElem_ne_zero : dxElem ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun (congrArg Subtype.val h) x
  simp only [dxElem, coe_derivationElem, Derivation.coeFn_coe, dx_x] at h1
  exact one_ne_zero h1

/-- A two-sided ideal of `D_ℚ(ℚ[x, x⁻¹])` containing `∂` contains `1`. -/
example (I : TwoSidedIdeal (DiffOp ℚ L)) (hI : dxElem ∈ I) : (1 : DiffOp ℚ L) ∈ I :=
  have := isSimpleRing L powersX_le
  IsSimpleRing.one_mem_of_ne_zero_mem I dxElem_ne_zero hI

/-- `∂ · ∂ ≠ 0` from the domain theorem. -/
example : dxElem * dxElem ≠ 0 :=
  have := isDomain L powersX_le
  mul_ne_zero dxElem_ne_zero dxElem_ne_zero

/-- Cross-check by evaluation: `∂²(x⁻¹) = 2 x⁻³`, which is nonzero. -/
example : ((dxElem * dxElem : DiffOp ℚ L) : Module.End ℚ L) xInv = 2 * (xInv * xInv * xInv) ∧
    2 * (xInv * xInv * xInv) ≠ 0 := by
  have hu : IsUnit xInv := IsUnit.of_mul_eq_one_right x x_mul_xInv
  refine ⟨?_, ?_⟩
  · simp only [dxElem, Subalgebra.coe_mul, coe_derivationElem, Module.End.mul_apply,
      Derivation.coeFn_coe, dx_xInv, map_neg, Derivation.leibniz, smul_eq_mul]
    ring
  · exact mul_ne_zero two_ne_zero ((hu.mul hu).mul hu).ne_zero

example : Infinite (Subring.center (DiffOp ℚ L)) := infinite_center L powersX_le

/-! ### The rational function field `ℚ(x₀, x₁)` -/

/-- The rational function field in two variables. -/
abbrev K2 := FractionRing (MvPolynomial (Fin 2) ℚ)

example : IsSimpleRing (DiffOp ℚ K2) :=
  isSimpleRing (S := nonZeroDivisors (MvPolynomial (Fin 2) ℚ)) K2 le_rfl
example : IsDomain (DiffOp ℚ K2) :=
  isDomain (S := nonZeroDivisors (MvPolynomial (Fin 2) ℚ)) K2 le_rfl
example : Module.DevLE (DiffOp ℚ K2)ᵐᵒᵖ (2 + 2) (DiffOp ℚ K2) :=
  devLE_right (nonZeroDivisors _) K2

/-! ### Injectivity of the symbol, against a direct computation -/

/-- `∂ = d/dx` on `ℚ[x]`. -/
noncomputable abbrev d : Derivation ℚ P1 P1 := pderiv 0

/-- Library: `ev(ξ²) = ∂²` does not have order one, since `ξ²` is a nonzero
homogeneous polynomial of degree two. -/
theorem d_sq_not_mem_order_one :
    d.toLinearMap * d.toLinearMap ∉ order (k := ℚ) (R := P1) 1 := by
  intro h
  have hF := PolynomialOperators.isCoordinateFrame (k := ℚ) (n := 1)
  have hX : (X 0 * X 0 : MvPolynomial (Fin 1) P1).IsHomogeneous 2 :=
    (isHomogeneous_X _ 0).mul (isHomogeneous_X _ 0)
  have hev := RingFiltration.polynomialEval_monomial (multiplicationAlgHom ℚ P1)
    (fun i => derivationElem (pderiv i)) (Finsupp.single 0 2) 1
  have hz := hF.polynomialGenerators.eq_zero_of_polynomialEval_mem_below
    hF.derivationElem_commutator multiplicationAlgHom_injective 2 _ hX ?_
  · exact X_ne_zero 0 (mul_self_eq_zero.mp hz)
  · rw [show (X 0 * X 0 : MvPolynomial (Fin 1) P1) = monomial (Finsupp.single 0 2) 1 by
      rw [← pow_two, X_pow_eq_monomial], hev, map_one, one_mul]
    rw [mem_orderFiltration_below]
    have hlen : (RingFiltration.monomialList (Finsupp.single (0 : Fin 1) 2)).length = 2 := by
      rw [RingFiltration.length_monomialList]
      simp [Finsupp.weight_apply]
    have : RingFiltration.monomialList (Finsupp.single (0 : Fin 1) 2) = List.replicate 2 0 :=
      List.eq_replicate_iff.mpr ⟨hlen, fun _ _ => Subsingleton.elim _ _⟩
    simpa [RingFiltration.monomialProd, this] using h

/-- Independent check: `[[∂², x], x] = 2`, which is not zero, so `∂²` is not
of order one. -/
example : commutator (commutator (d.toLinearMap * d.toLinearMap) (X 0 : P1)) (X 0) =
    (2 : ℚ) • (1 : Module.End ℚ P1) := by
  refine LinearMap.ext fun f => ?_
  simp only [commutator_apply, Module.End.mul_apply, Derivation.coeFn_coe, Derivation.leibniz,
    d, pderiv_X_self, smul_eq_mul, mul_one, map_add, LinearMap.smul_apply, Module.End.one_apply]
  rw [two_smul]
  ring

#print axioms LocalizedPolynomialOperators.isCoordinateFrame
#print axioms LocalizedPolynomialOperators.isSimpleRing
#print axioms LocalizedPolynomialOperators.isDomain
#print axioms LocalizedPolynomialOperators.devLE_right
#print axioms LocalizedPolynomialOperators.devLE_left
#print axioms LocalizedPolynomialOperators.infinite_center
#print axioms RingFiltration.PolynomialGenerators.gradedSymbol
#print axioms IsCoordinateFrame.isSimpleRing

end AlgebraicAnalysisTest.DifferentialOperatorsLocalized
