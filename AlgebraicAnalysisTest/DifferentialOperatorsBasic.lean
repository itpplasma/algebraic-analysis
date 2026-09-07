import AlgebraicAnalysis.DifferentialOperators.Basic
import AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration
import Mathlib.RingTheory.Derivation.Basic

open AlgebraicAnalysis.DifferentialOperators

variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

example (a x : R) : multiplication (k := k) a x = a * x := by
  rfl

example (a : R) :
    multiplication (k := k) a ∈ order (k := k) (R := R) 0 := by
  exact (mem_order_zero_iff_eq_multiplication _).2 (by
    ext x
    simp [multiplication_apply])

example (P : End (k := k) (R := R)) (a : R) :
    commutator P a = P * multiplication a - multiplication a * P := by
  rfl

example {P Q : End (k := k) (R := R)} {m n : ℕ}
    (hP : P ∈ order (k := k) (R := R) m)
    (hQ : Q ∈ order (k := k) (R := R) n) :
    P * Q ∈ order (k := k) (R := R) (m + n) := by
  exact mul_mem_order hP hQ

example (P : End (k := k) (R := R))
    (hP : P ∈ algebra (k := k) (R := R)) :
    ∃ n, P ∈ order (k := k) (R := R) n := by
  exact (mem_algebra_iff P).1 hP

example (a : R) :
    multiplication (k := k) a ∈ algebra (k := k) (R := R) := by
  exact multiplication_mem_algebra a

example (D : Derivation k R R) :
    D.toLinearMap ∈ algebra (k := k) (R := R) := by
  exact AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration.derivation_mem_algebra D

#print axioms AlgebraicAnalysis.DifferentialOperators.mul_mem_order
#print axioms AlgebraicAnalysis.DifferentialOperators.multiplication_mem_algebra
#print axioms AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration.derivation_mem_algebra
