module
public import AlgebraicAnalysis.DifferentialOperators.Basic
public import AlgebraicAnalysis.Filtration.PolynomialPresentation
public import Mathlib.RingTheory.Derivation.Basic

@[expose] public section

/-!
# The order filtration of the ring of differential operators

For a commutative `k`-algebra `R`, the ring `D = D_k(R)` of finite-order
`k`-linear differential operators (`DifferentialOperators.algebra`) is
filtered by order. This file packages the filtration and proves the two
basic structural facts of Grothendieck's theory, for every commutative `R`:

* **Commutators drop the order.** If `P` has order at most `m` and `Q` order
  at most `n`, then `PQ - QP` has order at most `m + n - 1`, and `PQ = QP`
  when `m = n = 0` (`mul_sub_mul_mem_orderBelow`). Hence the associated graded
  module of the order filtration is commutative
  (`orderFiltration_grCommutative`).
* **First-order operators.** `D₁ = R ⊕ Der_k(R)` as `k`-modules:
  `P ↦ (P 1, P - P(1))` (`orderOneEquiv`). In particular `D₁/D₀ ≅ Der_k(R)`.

The statement `[D_m, D_n] ⊆ D_{m+n-1}` is written with `orderBelow`, the
order filtration shifted by one (`orderBelow 0 = 0`,
`orderBelow (n + 1) = order n`). An operator has order at most `n` exactly
when all its commutators with multiplications lie in `orderBelow n`
(`mem_order_iff_commutator_mem_orderBelow`).

## Main definitions

* `DifferentialOperators.orderBelow`: the shifted order filtration.
* `DifferentialOperators.orderOneToDerivation`, `orderOneEquiv`: first-order
  operators.
* `DifferentialOperators.orderFiltration`: the order filtration of
  `D_k(R)` as a `RingFiltration k (algebra (k := k) (R := R))`.

## References

[EGA IV] A. Grothendieck, *Éléments de géométrie algébrique IV*, 16.8.
[StacksD] The Stacks Project, Section 10.133 (tag 09CH).
The proofs are AA-native, by induction on the order using the Jacobi identity
`[[P, Q], a] = [P, [Q, a]] + [[P, a], Q]`.
-/

namespace AlgebraicAnalysis.DifferentialOperators

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-! ## Linearity of the commutator -/

theorem commutator_add (P Q : End (k := k) (R := R)) (a : R) :
    commutator (P + Q) a = commutator P a + commutator Q a := by
  ext x
  simp only [commutator_apply, LinearMap.add_apply, mul_add]
  abel

theorem commutator_sub (P Q : End (k := k) (R := R)) (a : R) :
    commutator (P - Q) a = commutator P a - commutator Q a := by
  ext x
  simp only [commutator_apply, LinearMap.sub_apply, mul_sub]
  abel

theorem commutator_smul (c : k) (P : End (k := k) (R := R)) (a : R) :
    commutator (c • P) a = c • commutator P a := by
  ext x
  simp [commutator_apply, smul_sub]

theorem commutator_nsmul (m : ℕ) (P : End (k := k) (R := R)) (a : R) :
    commutator (m • P) a = m • commutator P a := by
  ext x
  simp [commutator_apply, smul_sub, nsmul_eq_mul, mul_left_comm]

theorem commutator_sum {ι : Type*} (s : Finset ι) (P : ι → End (k := k) (R := R)) (a : R) :
    commutator (∑ i ∈ s, P i) a = ∑ i ∈ s, commutator (P i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => ext; simp [commutator_apply]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, commutator_add, ih]

/-- Commutators with two multiplications can be taken in either order. -/
theorem commutator_commutator_comm (P : End (k := k) (R := R)) (a b : R) :
    commutator (commutator P a) b = commutator (commutator P b) a := by
  ext x
  simp only [commutator_apply]
  rw [mul_left_comm a b x]
  ring

theorem multiplication_mul (a b : R) :
    multiplication (k := k) (a * b) = multiplication a * multiplication b := by
  ext x
  simp [mul_assoc]

/-- Leibniz rule for the commutator in the multiplication argument. -/
theorem commutator_mul_right (P : End (k := k) (R := R)) (a b : R) :
    commutator P (a * b) =
      commutator P a * multiplication b + multiplication a * commutator P b := by
  ext x
  simp only [commutator_apply, LinearMap.add_apply, Module.End.mul_apply,
    multiplication_apply]
  ring_nf

/-- The commutator of a derivation with a multiplication is multiplication by
the derivative. -/
theorem commutator_derivation (D : Derivation k R R) (a : R) :
    commutator D.toLinearMap a = multiplication (D a) := by
  ext x
  simp [commutator_apply, Derivation.leibniz, mul_comm]

theorem multiplication_mem_order_zero (a : R) :
    multiplication (k := k) a ∈ order (k := k) (R := R) 0 := by
  rw [mem_order_zero_iff_eq_multiplication]
  ext x
  simp

/-! ## The shifted order filtration -/

/-- The order filtration shifted by one: `orderBelow 0 = 0` and
`orderBelow (n + 1) = order n`. -/
def orderBelow : ℕ → Submodule k (End (k := k) (R := R))
  | 0 => ⊥
  | n + 1 => order n

@[simp] theorem orderBelow_zero : orderBelow (k := k) (R := R) 0 = ⊥ := rfl

@[simp] theorem orderBelow_succ (n : ℕ) :
    orderBelow (k := k) (R := R) (n + 1) = order n := rfl

theorem orderBelow_le (n : ℕ) : orderBelow (k := k) (R := R) n ≤ order n := by
  cases n with
  | zero => exact bot_le
  | succ n => exact order_mono_step n

/-- An operator has order at most `n` iff its commutators with all
multiplications lie in `orderBelow n`. -/
theorem mem_order_iff_commutator_mem_orderBelow {P : End (k := k) (R := R)} {n : ℕ} :
    P ∈ order n ↔ ∀ a, commutator P a ∈ orderBelow n := by
  cases n with
  | zero => simp
  | succ n => exact mem_order_succ_iff P n

/-- `orderBelow n` is stable under composition with multiplications on the left. -/
theorem multiplication_mul_mem_orderBelow {Q : End (k := k) (R := R)} {n : ℕ} (a : R)
    (hQ : Q ∈ orderBelow n) : multiplication a * Q ∈ orderBelow n := by
  cases n with
  | zero =>
      rw [orderBelow_zero, Submodule.mem_bot] at hQ ⊢
      rw [hQ, mul_zero]
  | succ n => simpa using mul_mem_order (multiplication_mem_order_zero a) hQ

/-- `orderBelow n` is stable under composition with multiplications on the right. -/
theorem mul_multiplication_mem_orderBelow {Q : End (k := k) (R := R)} {n : ℕ} (a : R)
    (hQ : Q ∈ orderBelow n) : Q * multiplication a ∈ orderBelow n := by
  cases n with
  | zero =>
      rw [orderBelow_zero, Submodule.mem_bot] at hQ ⊢
      rw [hQ, zero_mul]
  | succ n => simpa using mul_mem_order hQ (multiplication_mem_order_zero a)

/-! ## Commutators drop the order -/

/-- **`[D_m, D_n] ⊆ D_{m+n-1}`.** If `P` has order at most `m` and `Q` order at
most `n`, then `PQ - QP` lies in `orderBelow (m + n)`: it has order at most
`m + n - 1`, and it vanishes when `m = n = 0`. -/
theorem mul_sub_mul_mem_orderBelow {P Q : End (k := k) (R := R)} {m n : ℕ}
    (hP : P ∈ order m) (hQ : Q ∈ order n) : P * Q - Q * P ∈ orderBelow (m + n) := by
  induction m generalizing n P Q with
  | zero =>
      rw [mem_order_zero_iff_eq_multiplication] at hP
      have hcomm : P * Q - Q * P = -commutator Q (P 1) := by
        rw [commutator, ← hP, neg_sub]
      rw [hcomm, zero_add]
      exact neg_mem (mem_order_iff_commutator_mem_orderBelow.mp hQ _)
  | succ m ihm =>
      induction n generalizing Q with
      | zero =>
          rw [mem_order_zero_iff_eq_multiplication] at hQ
          have hcomm : P * Q - Q * P = commutator P (Q 1) := by
            rw [commutator, ← hQ]
          rw [hcomm, add_zero]
          exact mem_order_iff_commutator_mem_orderBelow.mp hP _
      | succ n ihn =>
          rw [show m + 1 + (n + 1) = (m + n + 1) + 1 by omega, orderBelow_succ,
            mem_order_succ_iff]
          intro a
          have hPa := (mem_order_succ_iff P m).mp hP a
          have hQa := (mem_order_succ_iff Q n).mp hQ a
          have key : commutator (P * Q - Q * P) a =
              (P * commutator Q a - commutator Q a * P) +
                (commutator P a * Q - Q * commutator P a) := by
            rw [commutator_sub, commutator_mul, commutator_mul]
            abel
          rw [key]
          have h₁ := ihn hQa
          have h₂ := ihm hPa hQ
          rw [show m + 1 + n = (m + n) + 1 by omega, orderBelow_succ] at h₁
          rw [show m + (n + 1) = (m + n) + 1 by omega, orderBelow_succ] at h₂
          exact add_mem h₁ h₂

/-! ## First-order operators -/

/-- A derivation is a differential operator of order at most one. -/
theorem derivation_mem_order_one (D : Derivation k R R) :
    D.toLinearMap ∈ order (k := k) (R := R) 1 := by
  rw [mem_order_succ_iff]
  intro a
  rw [commutator_derivation]
  exact multiplication_mem_order_zero _

/-- An operator of order at most one killing `1` satisfies the Leibniz rule. -/
theorem leibniz_of_mem_order_one {Q : End (k := k) (R := R)} (hQ : Q ∈ order 1)
    (hQ1 : Q 1 = 0) (a b : R) : Q (a * b) = a * Q b + b * Q a := by
  have h := (mem_order_zero_iff_eq_multiplication _).mp ((mem_order_succ_iff Q 0).mp hQ a)
  have hb := LinearMap.congr_fun h b
  simp only [commutator_apply, multiplication_apply, mul_one, hQ1, mul_zero, sub_zero] at hb
  rw [mul_comm (Q a) b] at hb
  exact sub_eq_iff_eq_add'.mp hb

theorem sub_multiplication_mem_order_one {P : End (k := k) (R := R)} (hP : P ∈ order 1) :
    P - multiplication (P 1) ∈ order 1 :=
  sub_mem hP (order_mono_step 0 (multiplication_mem_order_zero _))

/-- The derivation part `P - P(1)` of a first-order operator `P`. -/
noncomputable def orderOneToDerivation :
    order (k := k) (R := R) 1 →ₗ[k] Derivation k R R where
  toFun P := Derivation.mk' (P.1 - multiplication (P.1 1)) fun a b => by
    have h := leibniz_of_mem_order_one (Q := P.1 - multiplication (P.1 1))
      (sub_multiplication_mem_order_one P.2) (by simp) a b
    simpa only [smul_eq_mul] using h
  map_add' P Q := by
    ext a
    simp only [Derivation.coe_mk', Submodule.coe_add, LinearMap.sub_apply, LinearMap.add_apply,
      multiplication_apply, Derivation.add_apply]
    ring
  map_smul' c P := by
    ext a
    simp only [Derivation.coe_mk', Submodule.coe_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      multiplication_apply, RingHom.id_apply, Derivation.smul_apply]
    rw [smul_sub, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    ring

@[simp] theorem orderOneToDerivation_apply (P : order (k := k) (R := R) 1) (a : R) :
    orderOneToDerivation P a = P.1 a - a * P.1 1 := by
  simp [orderOneToDerivation, mul_comm]

/-- Every first-order operator is a multiplication plus a derivation:
`P = P(1) + (P - P(1))`. -/
theorem eq_multiplication_add_orderOneToDerivation (P : order (k := k) (R := R) 1) :
    P.1 = multiplication (P.1 1) + (orderOneToDerivation P).toLinearMap := by
  ext a
  simp [mul_comm]

/-- **`D₁ = R ⊕ Der_k(R)`.** First-order operators are, as a `k`-module, the
direct sum of the multiplications and the derivations, by
`P ↦ (P 1, P - P(1))` with inverse `(a, D) ↦ a + D`. -/
noncomputable def orderOneEquiv :
    order (k := k) (R := R) 1 ≃ₗ[k] R × Derivation k R R where
  toFun P := (P.1 1, orderOneToDerivation P)
  map_add' P Q := by simp
  map_smul' c P := by simp
  invFun p := ⟨multiplication p.1 + p.2.toLinearMap,
    add_mem (order_mono_step 0 (multiplication_mem_order_zero _))
      (derivation_mem_order_one p.2)⟩
  left_inv P := by
    apply Subtype.ext
    exact (eq_multiplication_add_orderOneToDerivation P).symm
  right_inv p := by
    obtain ⟨a, D⟩ := p
    refine Prod.ext (by simp) ?_
    ext b
    have h1 : D.toLinearMap 1 = 0 := D.map_one_eq_zero
    simp only [orderOneToDerivation_apply, LinearMap.add_apply, multiplication_apply, mul_one,
      h1, add_zero]
    simp only [Derivation.coeFn_coe]
    ring

@[simp] theorem orderOneEquiv_apply (P : order (k := k) (R := R) 1) :
    orderOneEquiv P = (P.1 1, orderOneToDerivation P) := rfl

/-! ## The order filtration -/

/-- The order filtration of the ring `D_k(R)` of finite-order differential
operators: `F n` is the set of operators of order at most `n`. -/
def orderFiltration : RingFiltration k (algebra (k := k) (R := R)) where
  F n := (order n).comap (algebra (k := k) (R := R)).val.toLinearMap
  mono _ _ h _ hx := order_mono h hx
  one_mem := (mem_order_zero_iff_eq_multiplication _).mpr (by ext; simp)
  mul_le i j := Submodule.mul_le.mpr fun _ hx _ hy => mul_mem_order hx hy
  exhaustive := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨n, hn⟩ := x.2
    exact Submodule.mem_iSup_of_mem (ι := ℕ) n hn

@[simp] theorem mem_orderFiltration_F {x : algebra (k := k) (R := R)} {n : ℕ} :
    x ∈ (orderFiltration (k := k) (R := R)).F n ↔ (x : End (k := k) (R := R)) ∈ order n :=
  Iff.rfl

theorem mem_orderFiltration_below {x : algebra (k := k) (R := R)} {n : ℕ} :
    x ∈ (orderFiltration (k := k) (R := R)).below n ↔
      (x : End (k := k) (R := R)) ∈ orderBelow n := by
  cases n with
  | zero =>
      simp only [RingFiltration.below_zero, Submodule.mem_bot, orderBelow_zero]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  | succ n => exact Iff.rfl

/-- **The associated graded ring of `D_k(R)` is commutative**: for operators
of orders at most `i` and `j`, `PQ - QP` lies below order `i + j`. -/
theorem orderFiltration_grCommutative :
    (orderFiltration (k := k) (R := R)).GrCommutative := by
  intro i j x y hx hy
  rw [mem_orderFiltration_below]
  exact mul_sub_mul_mem_orderBelow hx hy

end AlgebraicAnalysis.DifferentialOperators
