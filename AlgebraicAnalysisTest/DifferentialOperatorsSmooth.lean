module
public import AlgebraicAnalysis.DifferentialOperators.SmoothOperators
public import AlgebraicAnalysis.DifferentialOperators.PolynomialOperators
public import AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialOperators
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

/-!
Oracles for differential operators on smooth algebras (stage D3).

* **Symbol multiplicativity, by hand.** On `ℚ[x]`, `ad_x² (∂²)` is computed by
  direct evaluation (`[∂², x] = 2∂`, `[[∂², x], x] = 2`) and agrees with the
  library formula `ad_x^{1+1}(∂ ∂) = (2 choose 1) ad_x ∂ · ad_x ∂`.
* **A hand-made projective frame** of `ℚ[x]`: `(x, ∂)`, where
  `d p = p' dx` is checked through the universal property. The library Euler
  identity then gives, for `P = ∂²` and `b = x²`, that
  `[∂², x²] - 2x [∂², x]` has order zero; direct evaluation shows it is
  multiplication by `2`.
* **Independent routes agree.** For `ℚ[x, y]` the smooth theory gives
  simplicity, domain and deviation at most `4`; the Weyl-algebra transport
  (`PolynomialOperators`) gives the same, by a different proof. For the
  Laurent polynomials `ℚ[x, x⁻¹]` (smooth as a localization) the smooth theory
  gives simplicity, independently of the degree argument of
  `LocalizedPolynomialOperators`, and deviation at most `4` (two generators
  `x`, `x⁻¹`), compatible with the sharper bound `2` from the coordinate frame.
* **Domain beyond finite type.** `D_ℚ(ℚ⟦X⟧)` is a domain by the polarization
  theorem; independently, `(d/dX)²` sends `X²` to `2 ≠ 0`.
* **Differential ideals.** The ideal `(x) ⊆ ℚ[x]` is not `∂`-stable, by the
  library (it would be the unit ideal) and by evaluation (`∂ x = 1 ∉ (x)`).
-/

namespace AlgebraicAnalysisTest.DifferentialOperatorsSmooth

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators MvPolynomial

/-- `ℚ[x]`. -/
abbrev P1 := MvPolynomial (Fin 1) ℚ

/-- `∂ = d/dx` on `ℚ[x]`. -/
noncomputable abbrev d : Derivation ℚ P1 P1 := pderiv 0

theorem d_X : d (X 0) = 1 := by simp [d]

/-! ### Symbol multiplicativity, by hand -/

/-- Hand computation: `ad_x² (∂²)` is multiplication by `2`. -/
theorem ad_sq_dd :
    (commutatorMap (X 0 : P1) ^ 2) (d.toLinearMap * d.toLinearMap) = multiplication 2 := by
  refine LinearMap.ext fun y => ?_
  simp only [pow_two, Module.End.mul_apply, commutatorMap_apply, commutator_apply,
    Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, d_X, multiplication_apply, map_add,
    mul_one]
  ring

/-- The library formula agrees: `ad_x^{1+1}(∂ ∂) = 2 (ad_x ∂)(ad_x ∂)`, and
`ad_x ∂ = 1`. -/
example : (commutatorMap (X 0 : P1) ^ 2) (d.toLinearMap * d.toLinearMap) 1 = 2 := by
  have h := commutatorMap_pow_mul_of_mem_order (k := ℚ) (X 0 : P1)
    (derivation_mem_order_one d) (derivation_mem_order_one d)
  have hd : (commutatorMap (X 0 : P1) ^ 1) d.toLinearMap = 1 := by
    rw [pow_one, commutatorMap_apply, commutator_derivation, d_X]
    ext y
    simp
  rw [show (1 : ℕ) + 1 = 2 from rfl, hd] at h
  rw [h]
  simp

example : (commutatorMap (X 0 : P1) ^ 2) (d.toLinearMap * d.toLinearMap) 1 = 2 := by
  rw [ad_sq_dd]
  simp

/-! ### A hand-made projective frame of `ℚ[x]` -/

/-- `(x, ∂)` is a projective frame of `ℚ[x]`: `d p = p' dx`. -/
theorem isProjectiveFrame_X :
    IsProjectiveFrame (fun _ : Fin 1 => (X 0 : P1)) (fun _ => d) := by
  refine ⟨by
    rw [show (Set.range fun _ : Fin 1 => (X 0 : P1)) = Set.range X by
      ext p; simp [Fin.exists_fin_one, eq_comm]]
    exact MvPolynomial.adjoin_range_X, fun p => ?_⟩
  have h : KaehlerDifferential.D ℚ P1 =
      (LinearMap.toSpanSingleton P1 _ (KaehlerDifferential.D ℚ P1 (X 0))).compDer d := by
    refine MvPolynomial.derivation_ext fun i => ?_
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    show KaehlerDifferential.D ℚ P1 (X 0) = d (X 0) • KaehlerDifferential.D ℚ P1 (X 0)
    rw [d_X, one_smul]
  simpa using Derivation.congr_fun h p

/-- Direct evaluation: `[∂², x²] - 2x [∂², x]` is multiplication by `2`. -/
theorem euler_oracle :
    commutator (d.toLinearMap * d.toLinearMap) (X 0 ^ 2) -
      multiplication (d (X 0 ^ 2)) * commutator (d.toLinearMap * d.toLinearMap) (X 0) =
      multiplication 2 := by
  refine LinearMap.ext fun y => ?_
  simp only [commutator_apply, LinearMap.sub_apply, Module.End.mul_apply, multiplication_apply,
    Derivation.coeFn_coe, pow_two, Derivation.leibniz, smul_eq_mul, d_X, map_add, mul_one]
  ring

/-- The library: the same operator lies in `orderBelow 1 = order 0`. -/
example : commutator (d.toLinearMap * d.toLinearMap) (X 0 ^ 2) -
    ∑ i : Fin 1, multiplication (d (X 0 ^ 2)) *
      commutator (d.toLinearMap * d.toLinearMap) ((fun _ : Fin 1 => (X 0 : P1)) i) ∈
      orderBelow (k := ℚ) (R := P1) 1 :=
  isProjectiveFrame_X.commutator_sub_sum_mem_orderBelow
    (by simpa using mul_mem_order (derivation_mem_order_one d) (derivation_mem_order_one d)) _

example : commutator (d.toLinearMap * d.toLinearMap) (X 0 ^ 2) -
    multiplication (d (X 0 ^ 2)) * commutator (d.toLinearMap * d.toLinearMap) (X 0) ∈
      order (k := ℚ) (R := P1) 0 := by
  rw [euler_oracle]
  exact multiplication_mem_order_zero _

/-! ### Independent routes agree: `ℚ[x, y]` -/

/-- `ℚ[x, y]`. -/
abbrev P2 := MvPolynomial (Fin 2) ℚ

example : IsSimpleRing (SmoothOperators.DiffOp ℚ P2) := SmoothOperators.isSimpleRing ℚ P2
example : IsSimpleRing (PolynomialOperators.DiffOp ℚ 2) := PolynomialOperators.isSimpleRing
example : IsDomain (SmoothOperators.DiffOp ℚ P2) := SmoothOperators.isDomain ℚ P2
example : IsNoetherianRing (SmoothOperators.DiffOp ℚ P2) := SmoothOperators.isNoetherianRing ℚ P2

/-- Deviation at most `2 + 2` from the two generators `x, y`, the same bound as
the coordinate route. -/
example : Module.DevLE (SmoothOperators.DiffOp ℚ P2)ᵐᵒᵖ (2 + 2) (SmoothOperators.DiffOp ℚ P2) :=
  SmoothOperators.devLE_right (MvPolynomial.adjoin_range_X (σ := Fin 2) (R := ℚ))

example : Module.DevLE (PolynomialOperators.DiffOp ℚ 2)ᵐᵒᵖ (2 + 2)
    (PolynomialOperators.DiffOp ℚ 2) :=
  PolynomialOperators.devLE_right

/-! ### Laurent polynomials -/

/-- `ℚ[x, x⁻¹]`. -/
abbrev L := Localization.Away (X 0 : P1)

instance : Algebra.Smooth ℚ L :=
  have : Algebra.Smooth P1 L := Algebra.Smooth.of_isLocalization_Away (X 0 : P1)
  Algebra.Smooth.comp ℚ P1 L

theorem powersX_le : Submonoid.powers (X 0 : P1) ≤ nonZeroDivisors P1 :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0)

instance : IsDomain L := IsLocalization.isDomain_localization powersX_le

/-- Smooth route. -/
example : IsSimpleRing (SmoothOperators.DiffOp ℚ L) := SmoothOperators.isSimpleRing ℚ L

/-- Degree route. -/
example : IsSimpleRing (LocalizedPolynomialOperators.DiffOp ℚ L) :=
  LocalizedPolynomialOperators.isSimpleRing L powersX_le

/-- `x` and `x⁻¹` generate `ℚ[x, x⁻¹]`, so the deviation is at most `2 + 2`. -/
example : Module.DevLE (SmoothOperators.DiffOp ℚ L)ᵐᵒᵖ (2 + 2) (SmoothOperators.DiffOp ℚ L) := by
  refine SmoothOperators.devLE_right (x := ![algebraMap P1 L (X 0),
    IsLocalization.Away.invSelf (X 0 : P1)]) (eq_top_iff.mpr fun b _ => ?_)
  obtain ⟨⟨p, s⟩, hb⟩ := IsLocalization.surj (Submonoid.powers (X 0 : P1)) b
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
  have hp : algebraMap P1 L p ∈ Algebra.adjoin ℚ (Set.range ![algebraMap P1 L (X 0),
      IsLocalization.Away.invSelf (X 0 : P1)]) := by
    have h := Algebra.adjoin_image ℚ (IsScalarTower.toAlgHom ℚ P1 L) (Set.range X)
    rw [MvPolynomial.adjoin_range_X, Algebra.map_top] at h
    have hmem : algebraMap P1 L p ∈ (⊤ : Subalgebra ℚ P1).map (IsScalarTower.toAlgHom ℚ P1 L) :=
      ⟨p, Algebra.mem_top, rfl⟩
    rw [Algebra.map_top, ← h] at hmem
    refine Algebra.adjoin_mono ?_ hmem
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact ⟨0, rfl⟩
  have hinv : IsLocalization.Away.invSelf (X 0 : P1) ∈ Algebra.adjoin ℚ
      (Set.range ![algebraMap P1 L (X 0), IsLocalization.Away.invSelf (X 0 : P1)]) :=
    Algebra.subset_adjoin ⟨1, rfl⟩
  have hb' : b = algebraMap P1 L p * IsLocalization.Away.invSelf (X 0 : P1) ^ n := by
    have hs : algebraMap P1 L s * IsLocalization.Away.invSelf (X 0 : P1) ^ n = 1 := by
      rw [← hn, map_pow, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
    rw [← hb, mul_assoc, hs, mul_one]
  rw [hb']
  exact Subalgebra.mul_mem _ hp (Subalgebra.pow_mem _ hinv n)

/-! ### A domain which is not of finite type -/

example : IsDomain (algebra (k := ℚ) (R := PowerSeries ℚ)) := DifferentialOperators.isDomain

/-- `(d/dX)² (X²) = 2`, so `(d/dX)²` is a nonzero product of nonzero operators. -/
example : ((PowerSeries.derivative (R := ℚ)).toLinearMap *
    (PowerSeries.derivative (R := ℚ)).toLinearMap)
    (PowerSeries.X ^ 2) = 2 := by
  simp only [Module.End.mul_apply, Derivation.coeFn_coe, Derivation.leibniz_pow,
    PowerSeries.derivative_X, smul_eq_mul, mul_one, map_nsmul]
  norm_num

/-! ### Differential ideals -/

/-- Library: `(x)` is not stable under `∂`, else it would be the unit ideal. -/
example : ¬ ∀ p ∈ Ideal.span {(X 0 : P1)}, d p ∈ Ideal.span {(X 0 : P1)} := by
  intro h
  have htop := eq_top_of_forall_pderiv_mem (Ideal.span {(X 0 : P1)})
    (by simp [X_ne_zero]) fun i => by
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact h
  rw [Ideal.span_singleton_eq_top, isUnit_iff_dvd_one] at htop
  obtain ⟨q, hq⟩ := htop
  have := congrArg (MvPolynomial.eval 0) hq
  simp at this

/-- Evaluation: `∂ x = 1 ∉ (x)`. -/
example : d (X 0) ∉ Ideal.span {(X 0 : P1)} := by
  rw [d_X, Ideal.mem_span_singleton]
  rintro ⟨q, hq⟩
  have := congrArg (MvPolynomial.eval 0) hq
  simp at this

#print axioms SmoothOperators.isNoetherian_right
#print axioms SmoothOperators.isNoetherianRing
#print axioms SmoothOperators.devLE_right
#print axioms SmoothOperators.devLE_left
#print axioms SmoothOperators.devLEOmega_right
#print axioms SmoothOperators.devLEOmega_left
#print axioms SmoothOperators.isSimpleRing
#print axioms SmoothOperators.isDomain
#print axioms SmoothOperators.infinite_center
#print axioms DifferentialOperators.isDomain
#print axioms eq_top_of_derivation_mem_of_smooth

end AlgebraicAnalysisTest.DifferentialOperatorsSmooth
