module
public import AlgebraicAnalysis.DifferentialOperators.PolynomialOperators

@[expose] public section

/-!
Oracles for the order filtration of `D_k(R)` and for `D_ℚ(ℚ[x])`.

Each oracle is an explicit computation with Mathlib's `pderiv` and polynomial
arithmetic, independent of the filtration and presentation machinery.

* First-order splitting: `x + ∂` splits as `(x, ∂)` under `orderOneEquiv`,
  computed by evaluating the operator.
* Commutator order is sharp: `[∂², x] = 2∂` by direct evaluation, so the bound
  `[D₂, D₀] ⊆ D₁` is attained; `2∂` has order one but not zero (`2∂(x) = 2`).
* Weyl isomorphism: the generator `∂` of `A₁(ℚ)` acts on `x²` as `2x`, and the
  generator `x` acts as multiplication by `x`.
* Simplicity: `∂ ≠ 0` (it sends `x` to `1`), so a two-sided ideal containing
  `∂` contains `1`.
* Domain: `∂ · ∂ ≠ 0` from the instance, cross-checked by `∂²(x²) = 2`.
* Dimension: the polynomial ring `ℚ[x]` has Krull dimension `1` (Mathlib's
  count of variables), which gives deviation at most `2` for `D_ℚ(ℚ[x])`.
-/

namespace AlgebraicAnalysisTest.DifferentialOperatorsPolynomial

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators
open AlgebraicAnalysis.DifferentialOperators.PolynomialOperators AlgebraicAnalysis.Weyl
open MvPolynomial

/-- The polynomial ring `ℚ[x]` in one variable. -/
abbrev P1 := MvPolynomial (Fin 1) ℚ

/-- The coordinate `x`. -/
noncomputable abbrev x : P1 := X 0

/-- The partial derivative `∂ = d/dx`. -/
noncomputable abbrev dx : Derivation ℚ P1 P1 := pderiv 0

/-! ### First-order operators -/

/-- `x + ∂` has order at most one. -/
theorem x_add_dx_mem : multiplication (k := ℚ) x + dx.toLinearMap ∈ order (k := ℚ) (R := P1) 1 :=
  add_mem (order_mono_step 0 (multiplication_mem_order_zero _)) (derivation_mem_order_one _)

/-- `orderOneEquiv (x + ∂) = (x, ∂)`. -/
example : orderOneEquiv ⟨_, x_add_dx_mem⟩ = (x, dx) := by
  refine Prod.ext ?_ ?_
  · simp
  · ext f
    simp only [orderOneEquiv_apply, orderOneToDerivation_apply, LinearMap.add_apply,
      multiplication_apply, mul_one, Derivation.coeFn_coe, dx, pderiv_one, add_zero]
    ring_nf

/-! ### Commutators drop the order, sharply -/

/-- Direct computation: `∂² x - x ∂² = 2 ∂` on `ℚ[x]`. -/
theorem dx_sq_comm_x :
    dx.toLinearMap * dx.toLinearMap * multiplication (k := ℚ) x -
        multiplication x * (dx.toLinearMap * dx.toLinearMap) = (2 : ℚ) • dx.toLinearMap := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, multiplication_apply,
    Derivation.coeFn_coe, LinearMap.smul_apply, Derivation.leibniz, dx, x, pderiv_X_self,
    smul_eq_mul, mul_one, map_add]
  rw [two_smul]
  ring

/-- The library bound: the commutator of an order-2 and an order-0 operator
lies in `orderBelow 2 = order 1`. -/
example : dx.toLinearMap * dx.toLinearMap * multiplication (k := ℚ) x -
    multiplication x * (dx.toLinearMap * dx.toLinearMap) ∈ order (k := ℚ) (R := P1) 1 :=
  mul_sub_mul_mem_orderBelow
    (mul_mem_order (derivation_mem_order_one dx) (derivation_mem_order_one dx))
    (multiplication_mem_order_zero x)

/-- The bound is attained: `2 ∂` does not have order zero, since an order-zero
operator is multiplication by its value at `1`, while `2 ∂ (1) = 0` and
`2 ∂ (x) = 2`. -/
example : (2 : ℚ) • dx.toLinearMap ∉ order (k := ℚ) (R := P1) 0 := by
  intro h
  have h1 := LinearMap.congr_fun ((mem_order_zero_iff_eq_multiplication _).mp h) x
  simp [dx, x] at h1

/-! ### The associated graded ring and the presentation -/

example : (orderFiltration (k := ℚ) (R := P1)).GrCommutative := orderFiltration_grCommutative

/-- `ℚ[x]` has Krull dimension one, so the symbol ring `ℚ[x][ξ]` has dimension two. -/
theorem ringKrullDim_P1 : ringKrullDim P1 = 1 := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    zero_add, Nat.card_fin]
  rfl

example : Module.DevLE (DiffOp ℚ 1)ᵐᵒᵖ 2 (DiffOp ℚ 1) := devLE_right
example : Module.DevLE (DiffOp ℚ 1) 2 (DiffOp ℚ 1) := devLE_left
example : Module.DevLEOmega (DiffOp ℚ 1)ᵐᵒᵖ (DiffOp ℚ 1) := devLEOmega_right
example : Module.DevLEOmega (DiffOp ℚ 1) (DiffOp ℚ 1) := devLEOmega_left
example : IsNoetherian (DiffOp ℚ 1)ᵐᵒᵖ (DiffOp ℚ 1) := isNoetherian_right
example : IsNoetherianRing (DiffOp ℚ 1) := isNoetherianRing

/-! ### The Weyl isomorphism -/

/-- The Weyl generator `∂` acts on `x²` as `2x`. -/
example : (weylEquiv ℚ 1 (generator ℚ 1 (.inr 0)) : Module.End ℚ P1) (x ^ 2) = 2 * x := by
  simp [weylGenerator, x]

/-- The Weyl generator `x` acts as multiplication by `x`. -/
example (f : P1) : (weylEquiv ℚ 1 (generator ℚ 1 (.inl 0)) : Module.End ℚ P1) f = x * f := by
  simp [weylGenerator]

/-! ### Simplicity, domain, centre -/

/-- `∂` as an element of `D_ℚ(ℚ[x])`. -/
noncomputable abbrev dxElem : DiffOp ℚ 1 := derivationElem dx

/-- `∂ ≠ 0`, because `∂ x = 1`. -/
theorem dxElem_ne_zero : dxElem ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun (congrArg Subtype.val h) x
  simp [dxElem, dx, x] at h1

/-- A two-sided ideal of `D_ℚ(ℚ[x])` containing `∂` contains `1`. -/
example (I : TwoSidedIdeal (DiffOp ℚ 1)) (hI : dxElem ∈ I) : (1 : DiffOp ℚ 1) ∈ I :=
  IsSimpleRing.one_mem_of_ne_zero_mem I dxElem_ne_zero hI

/-- `∂ · ∂ ≠ 0` from the domain instance. -/
example : dxElem * dxElem ≠ 0 := mul_ne_zero dxElem_ne_zero dxElem_ne_zero

/-- Cross-check by evaluation: `∂²(x²) = 2 ≠ 0`. -/
example : ((dxElem * dxElem : DiffOp ℚ 1) : Module.End ℚ P1) (x ^ 2) = 2 := by
  have h2 : dx (2 : P1) = 0 := by exact_mod_cast dx.map_natCast 2
  simp [dxElem, x, h2]

example : Infinite (Subring.center (DiffOp ℚ 1)) := infinite_center

#print axioms orderOneEquiv
#print axioms mul_sub_mul_mem_orderBelow
#print axioms orderFiltration_grCommutative
#print axioms DifferentialOperators.IsCoordinateFrame.polynomialGenerators
#print axioms RingFiltration.PolynomialGenerators.presentation
#print axioms PolynomialOperators.weylEquiv
#print axioms PolynomialOperators.isSimpleRing
#print axioms PolynomialOperators.isDomain
#print axioms PolynomialOperators.devLEOmega_right
#print axioms PolynomialOperators.devLEOmega_left
#print axioms PolynomialOperators.infinite_center

end AlgebraicAnalysisTest.DifferentialOperatorsPolynomial
