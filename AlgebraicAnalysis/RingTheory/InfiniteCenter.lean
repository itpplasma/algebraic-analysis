module
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

/-!
# Infinite centre of an infinite-dimensional-or-not algebra over an infinite field

Let `k` be an infinite field and `A` a nontrivial `k`-algebra. The structure map
`k → A` is injective (a ring map out of a field into a nontrivial ring) and its
image is central, because `k` acts through scalars. Hence the centre of `A`
contains an infinite set. This is the hypothesis `(Z)` of the filtered-ring
results: the centre is infinite.

## Main results

* `AlgebraicAnalysis.infinite_subring_center`: `Infinite (Subring.center A)`.
-/

namespace AlgebraicAnalysis

/-- **Infinite centre.** A nontrivial algebra over an infinite field has an
infinite centre. -/
theorem infinite_subring_center (k A : Type*) [Field k] [Infinite k] [Ring A]
    [Nontrivial A] [Algebra k A] : Infinite (Subring.center A) := by
  have hinj : Function.Injective (algebraMap k A) := (algebraMap k A).injective
  have hsub : Set.range (algebraMap k A) ⊆ (Subring.center A : Set A) := by
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subring.mem_center_iff]
    intro g
    exact (Algebra.commutes c g).symm
  exact Set.infinite_coe_iff.mpr ((Set.infinite_range_of_injective hinj).mono hsub)

end AlgebraicAnalysis
