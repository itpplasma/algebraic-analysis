import AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration

/-! Small consumer for the finite-order coordinate-generation variants.

Both theorems below independently reconstruct the historical
`mem_submodule_of_coordinates` / `mem_subalgebra_of_coordinates` statements
from the weaker, finite-order-only `hcoordinate` hypothesis of the primed
theorems, matching how a downstream project such as
`itpplasma/global-stafford-formal` is expected to consume them. -/

open AlgebraicAnalysis.DifferentialOperators
open AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration

variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

/-- Independent oracle: the primed submodule theorem, whose `hcoordinate`
hypothesis is only assumed for `algebra`-elements, still recovers the
original full-strength statement. -/
theorem submodule_of_coordinates_from_finite_order
    {n : ℕ} (x : Fin n → R) (D : Fin n → Derivation k R R)
    (hdual : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hcoordinate : ∀ P : Module.End k R,
      (∀ i, commutator P (x i) = 0) → P = multiplication (P 1))
    (H : Submodule k (Module.End k R))
    (hmul : ∀ r : R, multiplication r ∈ H)
    (hright : ∀ i Q, Q ∈ H → Q * (D i).toLinearMap ∈ H)
    (P : Module.End k R)
    (hP : P ∈ algebra (k := k) (R := R)) : P ∈ H :=
  mem_submodule_of_coordinates' x D hdual (fun P _ h => hcoordinate P h) H
    hmul hright P hP

/-- Independent oracle: the primed subalgebra theorem likewise recovers the
original full-strength statement. -/
theorem subalgebra_of_coordinates_from_finite_order
    {n : ℕ} (x : Fin n → R) (D : Fin n → Derivation k R R)
    (hdual : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hcoordinate : ∀ P : Module.End k R,
      (∀ i, commutator P (x i) = 0) → P = multiplication (P 1))
    (H : Subalgebra k (Module.End k R))
    (hmul : ∀ r : R, multiplication r ∈ H)
    (hder : ∀ i, (D i).toLinearMap ∈ H)
    (P : Module.End k R)
    (hP : P ∈ algebra (k := k) (R := R)) : P ∈ H :=
  mem_subalgebra_of_coordinates' x D hdual (fun P _ h => hcoordinate P h) H
    hmul hder P hP

#print axioms submodule_of_coordinates_from_finite_order
#print axioms subalgebra_of_coordinates_from_finite_order
