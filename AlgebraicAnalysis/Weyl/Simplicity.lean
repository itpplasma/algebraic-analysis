module
public import AlgebraicAnalysis.Weyl.Ore.PairStage
public import AlgebraicAnalysis.Weyl.IteratedEquivalence
public import Mathlib.RingTheory.SimpleRing.Congr
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

/-!
# Simplicity of the Weyl algebras in characteristic zero

The pair stage `B[x][∂; d/dx]` of a simple `k`-algebra `B` is simple when
`k` has characteristic zero.  The argument is the classical one for the Weyl
algebra.  Let `I` be a nonzero two-sided ideal.

* Commutation with the coordinate `x` lowers the `∂`-degree by one, with
  leading coefficient a nonzero integer multiple, so `I` meets the coordinate
  stage `B[x]`.
* Commutation with `∂` lowers the `x`-degree by one in the same way, so `I`
  meets the base `B`.
* `I ∩ B` is a nonzero two-sided ideal of `B`, hence contains `1`.

Induction over the tower `IteratedPairStage k n` and transport along the
presentation equivalence give `IsSimpleRing (WeylAlg k n)`.

Provenance: this file is new in `AlgebraicAnalysis`.  The tower and
presentation it applies are the copied Weyl development of this package.
-/

namespace AlgebraicAnalysis.Weyl.Simplicity

open AlgebraicAnalysis AlgebraicAnalysis.OreDivision AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.Weyl.Ore.CoordinateStage AlgebraicAnalysis.Weyl.Ore.PairStage
open Polynomial

noncomputable section

section Torsion

/-- A nonzero natural number is not a left zero divisor in a `k`-algebra over a
field of characteristic zero. -/
theorem eq_zero_of_natCast_mul (k : Type*) [Field k] [CharZero k] {A : Type*} [Ring A]
    [Algebra k A] {m : ℕ} (hm : m ≠ 0) {a : A}
    (h : (m : A) * a = 0) : a = 0 := by
  have hc : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr hm
  calc a = algebraMap k A ((m : k)⁻¹) * ((m : A) * a) := by
        rw [← mul_assoc, ← map_natCast (algebraMap k A) m, ← map_mul,
          inv_mul_cancel₀ hc, map_one, one_mul]
    _ = 0 := by rw [h, mul_zero]

/-- A nonzero natural number is not a right zero divisor in a `k`-algebra over a
field of characteristic zero. -/
theorem eq_zero_of_mul_natCast (k : Type*) [Field k] [CharZero k] {A : Type*} [Ring A]
    [Algebra k A] {m : ℕ} (hm : m ≠ 0) {a : A}
    (h : a * (m : A) = 0) : a = 0 := by
  have hc : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr hm
  calc a = (a * (m : A)) * algebraMap k A ((m : k)⁻¹) := by
        rw [← map_natCast (algebraMap k A) m, mul_assoc, ← map_mul,
          mul_inv_cancel₀ hc, map_one, mul_one]
    _ = 0 := by rw [h, zero_mul]

end Torsion

section Stage

variable {B : Type*} [Ring B]

/-- Nonzero natural multiples are not right zero divisors in the coordinate
stage, which carries its scalar algebra structure from a `k`-algebra `B`. -/
theorem coordinateStage_eq_zero_of_mul_natCast (k : Type*) [Field k] [CharZero k]
    [Algebra k B] {m : ℕ} (hm : m ≠ 0)
    {s : CoordinateStage (B := B)} (h : s * (m : CoordinateStage (B := B)) = 0) :
    s = 0 := by
  letI : Algebra k (CoordinateStage (B := B)) := coordinateStageAlgebra
  exact eq_zero_of_mul_natCast k hm h

/-- The central coordinate commutes with every element of the coordinate
stage.  This is the commutativity of `X` with `B[X]`, transported through the
normal form. -/
theorem variable_mul_coordinate_comm (s : CoordinateStage (B := B)) :
    normalVariable (zeroDerivation : OreDivisionDerivation B) * s =
      s * normalVariable (zeroDerivation : OreDivisionDerivation B) := by
  obtain ⟨p, rfl⟩ := normalForm_surjective zeroDerivation s
  rw [normalVariable, ← normalForm_mul_zeroDerivation, ← normalForm_mul_zeroDerivation,
    (Polynomial.commute_X p).eq]

/-- The pair coordinate commutes with every coefficient of the pair stage. -/
theorem pairCoordinate_comm_coefficient (s : CoordinateStage (B := B)) :
    pairCoordinate (B := B) * normalCoefficient (outerD (B := B)) s =
      normalCoefficient (outerD (B := B)) s * pairCoordinate (B := B) := by
  unfold pairCoordinate
  rw [← map_mul, ← map_mul, variable_mul_coordinate_comm]

/-- The momentum and coordinate of a Weyl pair satisfy `∂ x = x ∂ + 1`. -/
theorem pairMomentum_mul_pairCoordinate :
    pairMomentum (B := B) * pairCoordinate (B := B) =
      pairCoordinate (B := B) * pairMomentum (B := B) + 1 := by
  have h := normalVariable_mul_coefficient (outerD (B := B))
    (normalVariable (zeroDerivation : OreDivisionDerivation B))
  rw [coordinateDerivation_variable, map_one] at h
  exact h

set_option maxHeartbeats 3200000 in
/-- Iterated commutator of the momentum with the coordinate:
`∂^(j+1) x = x ∂^(j+1) + (j+1) ∂^j`. -/
theorem pairMomentum_pow_mul_pairCoordinate (j : ℕ) :
    pairMomentum (B := B) ^ (j + 1) * pairCoordinate (B := B) =
      pairCoordinate (B := B) * pairMomentum (B := B) ^ (j + 1) +
        ((j + 1 : ℕ) : PairStage (B := B)) * pairMomentum (B := B) ^ j := by
  induction j with
  | zero => simpa using pairMomentum_mul_pairCoordinate (B := B)
  | succ j ih =>
    have hc : pairMomentum (B := B) * ((j + 1 : ℕ) : PairStage (B := B)) =
        ((j + 1 : ℕ) : PairStage (B := B)) * pairMomentum (B := B) :=
      (Nat.cast_commute (j + 1) _).symm.eq
    calc pairMomentum (B := B) ^ (j + 1 + 1) * pairCoordinate (B := B)
        = pairMomentum (B := B) * (pairMomentum (B := B) ^ (j + 1) *
            pairCoordinate (B := B)) := by rw [pow_succ', mul_assoc]
      _ = pairMomentum (B := B) * (pairCoordinate (B := B) *
            pairMomentum (B := B) ^ (j + 1) +
            ((j + 1 : ℕ) : PairStage (B := B)) * pairMomentum (B := B) ^ j) := by
          rw [ih]
      _ = (pairMomentum (B := B) * pairCoordinate (B := B)) *
            pairMomentum (B := B) ^ (j + 1) +
            ((j + 1 : ℕ) : PairStage (B := B)) * (pairMomentum (B := B) *
              pairMomentum (B := B) ^ j) := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hc,
            mul_assoc (((j + 1 : ℕ) : PairStage (B := B))) pairMomentum]
      _ = (pairCoordinate (B := B) * pairMomentum (B := B) + 1) *
            pairMomentum (B := B) ^ (j + 1) +
            ((j + 1 : ℕ) : PairStage (B := B)) * pairMomentum (B := B) ^ (j + 1) := by
          rw [pairMomentum_mul_pairCoordinate,
            ← pow_succ' (pairMomentum (B := B)) j]
      _ = pairCoordinate (B := B) * pairMomentum (B := B) ^ (j + 1 + 1) +
            ((j + 1 + 1 : ℕ) : PairStage (B := B)) * pairMomentum (B := B) ^ (j + 1) := by
          rw [add_mul, one_mul, mul_assoc,
            ← pow_succ' (pairMomentum (B := B)) (j + 1), Nat.cast_succ (j + 1), add_mul,
            one_mul, add_assoc, add_comm (pairMomentum (B := B) ^ (j + 1))]

set_option maxHeartbeats 3200000 in
/-- Commutation with the coordinate lowers the momentum degree of a normal
form: `x p(∂) - p(∂) x = -p'(∂)`. -/
theorem pairCoordinate_comm_normalForm (p : Polynomial (CoordinateStage (B := B))) :
    pairCoordinate (B := B) * normalForm (outerD (B := B)) p -
        normalForm (outerD (B := B)) p * pairCoordinate (B := B) =
      normalForm (outerD (B := B)) (-derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [normalForm_add, derivative_add, neg_add, normalForm_add, ← hp, ← hq]
    noncomm_ring
  | monomial j s =>
    rcases j with _ | j
    · simp only [normalForm_monomial, pow_zero, mul_one, Nat.cast_zero, mul_zero,
        derivative_monomial, monomial_zero_right, normalForm_zero, neg_zero]
      exact sub_eq_zero.mpr (pairCoordinate_comm_coefficient s)
    · have hx : pairCoordinate (B := B) * normalCoefficient (outerD (B := B)) s =
          normalCoefficient (outerD (B := B)) s * pairCoordinate (B := B) :=
        pairCoordinate_comm_coefficient s
      rw [derivative_monomial, normalForm_neg, normalForm_monomial, normalForm_monomial,
        Nat.add_sub_cancel, map_mul, map_natCast (normalCoefficient (outerD (B := B))),
        show normalVariable (outerD (B := B)) = pairMomentum (B := B) from rfl]
      have h1 : pairCoordinate (B := B) * (normalCoefficient (outerD (B := B)) s *
          pairMomentum (B := B) ^ (j + 1)) =
          normalCoefficient (outerD (B := B)) s *
            (pairCoordinate (B := B) * pairMomentum (B := B) ^ (j + 1)) := by
        rw [← mul_assoc, hx, mul_assoc]
      have h2 : normalCoefficient (outerD (B := B)) s * pairMomentum (B := B) ^ (j + 1) *
          pairCoordinate (B := B) =
          normalCoefficient (outerD (B := B)) s * (pairMomentum (B := B) ^ (j + 1) *
            pairCoordinate (B := B)) := by
        rw [mul_assoc]
      rw [h1, h2, pairMomentum_pow_mul_pairCoordinate j, mul_add, mul_assoc
        (normalCoefficient (outerD (B := B)) s)]
      abel

end Stage

section Descent

variable {B : Type*} [Ring B]

/-- The unit ring is nontrivial whenever the coefficient ring is. -/
theorem nontrivial_coordinateStage [Nontrivial B] :
    Nontrivial (CoordinateStage (B := B)) :=
  ⟨⟨normalForm zeroDerivation 1, 0, fun h =>
    one_ne_zero (normalForm_injective zeroDerivation (by rw [h, normalForm_zero]))⟩⟩

/-- The pair stage is nontrivial whenever the coefficient ring is. -/
theorem nontrivial_pairStage [Nontrivial B] : Nontrivial (PairStage (B := B)) := by
  haveI := nontrivial_coordinateStage (B := B)
  exact ⟨⟨normalForm (outerD (B := B)) 1, 0, fun h =>
    one_ne_zero (normalForm_injective (outerD (B := B)) (by rw [h, normalForm_zero]))⟩⟩

set_option maxHeartbeats 3200000 in
/-- **Coordinate descent.** A nonzero two-sided ideal of the pair stage meets the
coordinate stage `B[x]` in a nonzero element: commutation with the coordinate
`x` lowers the momentum degree of a normal form, with a nonzero integer
multiple of the leading coefficient. -/
theorem exists_coordinate_mem (k : Type*) [Field k] [CharZero k] [Algebra k B]
    (I : Ideal (PairStage (B := B))) (hI : I.IsTwoSided) (hne : I ≠ ⊥) :
    ∃ s : CoordinateStage (B := B), s ≠ 0 ∧
      normalCoefficient (outerD (B := B)) s ∈ I := by
  have key : ∀ d : ℕ, ∀ p : Polynomial (CoordinateStage (B := B)), p ≠ 0 →
      p.natDegree ≤ d → normalForm (outerD (B := B)) p ∈ I →
      ∃ s : CoordinateStage (B := B), s ≠ 0 ∧
        normalCoefficient (outerD (B := B)) s ∈ I := by
    intro d
    induction d with
    | zero =>
      intro p hp hdeg hpI
      refine ⟨p.coeff 0, ?_, ?_⟩
      · intro h
        apply hp
        rw [eq_C_of_natDegree_le_zero hdeg, h, C_0]
      · have hC : normalForm (outerD (B := B)) p =
            normalCoefficient (outerD (B := B)) (p.coeff 0) := by
          rw [← normalForm_C, ← eq_C_of_natDegree_le_zero hdeg]
        rw [← hC]
        exact hpI
    | succ d ih =>
      intro p hp hdeg hpI
      by_cases hle : p.natDegree ≤ d
      · exact ih p hp hle hpI
      · have hnd : p.natDegree = d + 1 := by omega
        have hlead : p.coeff (d + 1) ≠ 0 := by
          rw [← hnd]
          exact leadingCoeff_ne_zero.mpr hp
        have hder : (derivative p).coeff d ≠ 0 := by
          rw [coeff_derivative, ← Nat.cast_succ]
          exact fun h => hlead
            (coordinateStage_eq_zero_of_mul_natCast k (Nat.succ_ne_zero d) h)
        have hne' : -(derivative p) ≠ 0 := by
          refine neg_ne_zero.mpr ?_
          intro h
          apply hder
          rw [h, coeff_zero]
        have hmem : normalForm (outerD (B := B)) (-(derivative p)) ∈ I := by
          rw [← pairCoordinate_comm_normalForm]
          exact I.sub_mem (Ideal.mul_mem_left I _ hpI) (hI.mul_mem_of_left _ hpI)
        have hdeg' : (-(derivative p)).natDegree ≤ d := by
          rw [natDegree_neg]
          have := natDegree_derivative_le p
          omega
        exact ih _ hne' hdeg' hmem
  obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨p, rfl⟩ := normalForm_surjective (outerD (B := B)) r
  have hp : p ≠ 0 := by
    rintro rfl
    exact hr0 (normalForm_zero _)
  exact key p.natDegree p hp le_rfl hrI

set_option maxHeartbeats 3200000 in
/-- **Base descent.** If `B[x]` contains a nonzero element of a two-sided ideal of
the pair stage, then the base `B` contains a nonzero element of the same ideal
(after the scalar embedding): commutation with `∂` lowers the `x`-degree. -/
theorem exists_base_mem (k : Type*) [Field k] [CharZero k] [Algebra k B]
    (I : Ideal (PairStage (B := B))) (hI : I.IsTwoSided) :
    ∀ d : ℕ, ∀ q : Polynomial B, q ≠ 0 → q.natDegree ≤ d →
      normalCoefficient (outerD (B := B))
          (normalForm (zeroDerivation : OreDivisionDerivation B) q) ∈ I →
      ∃ b : B, b ≠ 0 ∧
        normalCoefficient (outerD (B := B))
          (normalCoefficient (zeroDerivation : OreDivisionDerivation B) b) ∈ I := by
  intro d
  induction d with
  | zero =>
    intro q hq hdeg hqI
    refine ⟨q.coeff 0, ?_, ?_⟩
    · intro h
      apply hq
      rw [eq_C_of_natDegree_le_zero hdeg, h, C_0]
    · have h0 : normalForm (zeroDerivation : OreDivisionDerivation B) q =
          normalCoefficient (zeroDerivation : OreDivisionDerivation B) (q.coeff 0) := by
        rw [← normalForm_C, ← eq_C_of_natDegree_le_zero hdeg]
      rw [h0] at hqI
      exact hqI
  | succ d ih =>
    intro q hq hdeg hqI
    by_cases hle : q.natDegree ≤ d
    · exact ih q hq hle hqI
    · have hnd : q.natDegree = d + 1 := by omega
      have hlead : q.coeff (d + 1) ≠ 0 := by
        rw [← hnd]
        exact leadingCoeff_ne_zero.mpr hq
      have hder : (derivative q).coeff d ≠ 0 := by
        rw [coeff_derivative, ← Nat.cast_succ]
        exact fun h => hlead (eq_zero_of_mul_natCast k (Nat.succ_ne_zero d) h)
      have hne' : derivative q ≠ 0 := fun h => hder (by rw [h, coeff_zero])
      have h := normalVariable_mul_coefficient (outerD (B := B))
        (normalForm (zeroDerivation : OreDivisionDerivation B) q)
      have e := eq_sub_of_add_eq' h.symm
      rw [coordinateDerivation_normalForm] at e
      have hmem : normalCoefficient (outerD (B := B))
          (normalForm (zeroDerivation : OreDivisionDerivation B) (derivative q)) ∈ I := by
        rw [e]
        exact I.sub_mem (Ideal.mul_mem_left I _ hqI) (hI.mul_mem_of_left _ hqI)
      have hdeg' : (derivative q).natDegree ≤ d := by
        have := natDegree_derivative_le q
        omega
      exact ih _ (by
        intro h0
        exact hne' h0) hdeg' hmem

set_option maxHeartbeats 3200000 in
/-- **The pair stage is simple.** If the coefficient ring `B` is simple and `k`
has characteristic zero, the pair stage `B[x][∂; d/dx]` is simple. -/
theorem isSimpleRing_pairStage (k : Type*) [Field k] [CharZero k] {B : Type*} [Ring B]
    [Algebra k B] [IsSimpleRing B] : IsSimpleRing (PairStage (B := B)) := by
  have hB : ∀ J : Ideal B, J.IsTwoSided → J = ⊥ ∨ J = ⊤ :=
    (isSimpleRing_iff_isTwoSided_imp.mp inferInstance).2
  haveI : Nontrivial (CoordinateStage (B := B)) := nontrivial_coordinateStage
  haveI : Nontrivial (PairStage (B := B)) := nontrivial_pairStage
  rw [isSimpleRing_iff_isTwoSided_imp]
  refine ⟨inferInstance, fun I hI => ?_⟩
  by_cases hbot : I = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨s, hs0, hsI⟩ := exists_coordinate_mem k I hI hbot
  obtain ⟨q, rfl⟩ := normalForm_surjective zeroDerivation s
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hs0 (normalForm_zero _)
  obtain ⟨b, hb0, hbI⟩ := exists_base_mem k I hI q.natDegree q hq0 le_rfl hsI
  have hJ : (Ideal.comap (pairCoefficient (B := B)) I).IsTwoSided := by
    refine ⟨fun {a} c ha => ?_⟩
    show pairCoefficient (B := B) (a * c) ∈ I
    rw [map_mul]
    exact hI.mul_mem_of_left _ ha
  rcases hB _ hJ with h | h
  · exfalso
    apply hb0
    have hbJ : b ∈ Ideal.comap (pairCoefficient (B := B)) I := hbI
    rw [h] at hbJ
    simpa using hbJ
  · have h1 : (1 : B) ∈ Ideal.comap (pairCoefficient (B := B)) I := by
      rw [h]
      exact Submodule.mem_top
    have h2 : pairCoefficient (B := B) 1 ∈ I := h1
    rw [map_one] at h2
    exact Ideal.eq_top_of_isUnit_mem I h2 isUnit_one

end Descent

section Tower

universe u

open AlgebraicAnalysis.Weyl.Ore.IteratedPairStage

/-- The iterated pair stages over a field of characteristic zero are simple. -/
theorem isSimpleRing_iteratedPairStage (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    IsSimpleRing (IteratedPairStage k n) := by
  induction n with
  | zero => exact DivisionRing.isSimpleRing k
  | succ n ih => exact isSimpleRing_pairStage k (B := IteratedPairStage k n)

/-- **Simplicity of the Weyl algebra.** For a field `k` of characteristic zero,
the presented Weyl algebra `A_n(k)` is simple. -/
theorem isSimpleRing_weylAlg (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    IsSimpleRing (WeylAlg k n) :=
  IsSimpleRing.of_ringEquiv
    (AlgebraicAnalysis.Weyl.IteratedEquivalence.presentedIteratedEquiv k n).toRingEquiv.symm
    (isSimpleRing_iteratedPairStage k n)

end Tower

end

end AlgebraicAnalysis.Weyl.Simplicity
