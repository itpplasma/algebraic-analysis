import Mathlib

/-!
# The central-coordinate escape kernel

This file contains the part of the central-coordinate escape argument which
is independent of the later Stafford module bookkeeping.  The coefficient
ring is a division ring `E`; `normal` is the coefficient-left PBW normal form
for a differential Ore extension `S`; and `commutator` is the additive map
`w ↦ w x - x w`.  The only Ore-specific input needed by the kernel is the
transport identity

`normal (derivative p) = commutator (normal p)`.

The resulting theorem says that iterating `ad(x)` by the PBW degree produces
the nonzero scalar `d! · lc(p)`, hence a unit.  The hypotheses are explicit so
that a later concrete Ore-stage file must prove the transport identity rather
than hiding it behind an axiom.

No module-span, simplicity, denominator, or geometric statement is included:
those are separate packet obligations.
-/

namespace AlgebraicAnalysis.Escape

open Polynomial

noncomputable section

set_option maxHeartbeats 400000

variable {E S : Type*} [DivisionRing E] [Ring S]

/-- The additive commutator map with a fixed right-hand coordinate `x`.

The orientation is the one used in the escape argument:
`adₓ(w) = w x - x w`.
-/
def commutator (x : S) : S →+ S where
  toFun w := w * x - x * w
  map_zero' := by simp
  map_add' w v := by simp [add_mul, mul_add, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm]

@[simp] theorem commutator_apply (x w : S) :
    commutator x w = w * x - x * w := rfl

/-- Correct central-coordinate PBW data for a differential Ore stage. -/
structure CentralEscapeData where
  /-- Coefficient-left normal form for the Ore stage. -/
  normal : Polynomial E ≃+ S
  /-- Ring embedding of coefficients into the Ore stage. -/
  embed : E →+* S
  /-- The central coefficient coordinate used by the commutator. -/
  coordinate : E
  normal_C : ∀ a : E, normal (C a) = embed a
  embed_isUnit : ∀ {a : E}, a ≠ 0 → IsUnit (embed a)
  ad_normal_derivative :
    ∀ p : Polynomial E,
      commutator (embed coordinate) (normal p) = normal (derivative p)

namespace CentralEscapeData

variable (D : CentralEscapeData (E := E) (S := S))

lemma iterate_commutator_normal (p : Polynomial E) (k : ℕ) :
    ((commutator (D.embed D.coordinate))^[k]) (D.normal p) =
      D.normal ((derivative^[k]) p) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        ((commutator (D.embed D.coordinate))^[k.succ]) (D.normal p) =
            commutator (D.embed D.coordinate)
              (((commutator (D.embed D.coordinate))^[k]) (D.normal p)) :=
          Function.iterate_succ_apply' _ _ _
        _ = commutator (D.embed D.coordinate) (D.normal ((derivative^[k]) p)) :=
          congrArg (commutator (D.embed D.coordinate)) ih
        _ = D.normal (derivative ((derivative^[k]) p)) :=
          D.ad_normal_derivative _
        _ = D.normal ((derivative^[k.succ]) p) := by
          rw [Function.iterate_succ_apply']

lemma iterate_derivative_natDegree (p : Polynomial E) :
    derivative^[p.natDegree] p =
      C ((Nat.factorial p.natDegree) • p.leadingCoeff) := by
  apply Polynomial.ext
  intro m
  by_cases hm : m = 0
  · subst m
    rw [coeff_iterate_derivative]
    simp only [Nat.zero_add, Nat.descFactorial_self, coeff_C_zero,
      smul_eq_mul, coeff_natDegree]
  · have hlt : p.natDegree < m + p.natDegree := by
      omega
    have hcoeff : p.coeff (m + p.natDegree) = 0 :=
      coeff_eq_zero_of_natDegree_lt hlt
    rw [coeff_iterate_derivative, hcoeff, smul_zero, coeff_C]
    simp [hm]

lemma factorial_leadingCoeff_ne_zero [CharZero E] {p : Polynomial E} (hp : p ≠ 0) :
    (Nat.factorial p.natDegree) • p.leadingCoeff ≠ 0 := by
  rw [nsmul_eq_mul']
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp)
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- One commutator lowers a nonconstant PBW polynomial's degree. -/
@[nolint unusedArguments]
lemma ad_degree_reduction [CharZero E] {p : Polynomial E}
    (hpositive : p.natDegree ≠ 0) :
    (derivative p).natDegree < p.natDegree ∧
      commutator (D.embed D.coordinate) (D.normal p) =
        D.normal (derivative p) := by
  exact ⟨natDegree_derivative_lt hpositive, D.ad_normal_derivative p⟩

/-- Iterated `ad(x)` produces a nonzero coefficient, hence a unit. -/
lemma ad_unit_production [CharZero E] {p : Polynomial E} (hp : p ≠ 0) :
    IsUnit
      (((commutator (D.embed D.coordinate))^[p.natDegree]) (D.normal p)) := by
  rw [iterate_commutator_normal D, iterate_derivative_natDegree]
  rw [D.normal_C]
  exact D.embed_isUnit (factorial_leadingCoeff_ne_zero hp)

end CentralEscapeData

/-! Axiom report for the proof-critical kernel. -/
#print axioms CentralEscapeData.iterate_derivative_natDegree
#print axioms CentralEscapeData.ad_degree_reduction
#print axioms CentralEscapeData.ad_unit_production

end
end AlgebraicAnalysis.Escape

