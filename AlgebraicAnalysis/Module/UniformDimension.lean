module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.SimpleModule.Basic

@[expose] public section

/-!
# Uniform dimension via independent families of submodules

The uniform (Goldie) dimension of a module `M` is the supremum of the numbers
`n` such that `M` contains a direct sum of `n` nonzero submodules. We record
the two one-sided comparisons as predicates on natural numbers, so that no
supremum and no finiteness hypothesis enters the definition:

* `Module.UniformDimGE R M n`: there are `n` nonzero submodules of `M` whose sum
  is direct (an `iSupIndep` family indexed by `Fin n`);
* `Module.UniformDimLE R M n`: there is no such family of `n + 1` submodules.

Right modules over a ring `R` are modules over `Rᵐᵒᵖ`, so the uniform dimension
of a right module `M` is `Module.UniformDimGE Rᵐᵒᵖ M`.

## Main results

* `Module.UniformDimGE.le_length`: a direct sum of `n` nonzero submodules forces
  `n ≤ length M`;
* `Module.uniformDimGE_iff_le_length`, `Module.uniformDimLE_iff_length_le`: for a
  semisimple module the uniform dimension is the length;
* `Module.UniformDimGE.mono`, `Module.uniformDimGE_congr`: monotonicity in `n` and
  invariance under linear equivalences.

## References

K. R. Goodearl and R. B. Warfield, *An Introduction to Noncommutative Noetherian
Rings*, 2nd ed., Chapter 5; J. C. McConnell and J. C. Robson, *Noncommutative
Noetherian Rings*, 2.2.10–2.2.12. Nothing here is new.
-/

namespace AlgebraicAnalysis.Module

universe u v w

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]

/-- `UniformDimGE R M n`: the uniform dimension of `M` is at least `n`, that is,
`M` contains `n` nonzero submodules whose sum is direct. -/
def UniformDimGE (n : ℕ) : Prop :=
  ∃ N : Fin n → Submodule R M, iSupIndep N ∧ ∀ i, N i ≠ ⊥

/-- `UniformDimLE R M n`: the uniform dimension of `M` is at most `n`, that is,
`M` contains no direct sum of `n + 1` nonzero submodules. -/
def UniformDimLE (n : ℕ) : Prop :=
  ¬ UniformDimGE R M (n + 1)

variable {R M}

/-- Every module has uniform dimension at least `0`. -/
theorem uniformDimGE_zero : UniformDimGE R M 0 :=
  ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-- If the uniform dimension is at least `n`, it is at least every `k ≤ n`. -/
theorem UniformDimGE.mono {n k : ℕ} (h : UniformDimGE R M n) (hk : k ≤ n) :
    UniformDimGE R M k := by
  obtain ⟨N, hN, hne⟩ := h
  exact ⟨N ∘ Fin.castLE hk, hN.comp (Fin.castLE_injective hk), fun i => hne _⟩

/-- A direct sum of `n` nonzero submodules is carried along a linear equivalence. -/
theorem UniformDimGE.of_linearEquiv {N : Type w} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    {n : ℕ} (h : UniformDimGE R M n) : UniformDimGE R N n := by
  obtain ⟨K, hK, hne⟩ := h
  let o := Submodule.orderIsoMapComap e
  refine ⟨fun i => o (K i), (iSupIndep_map_orderIso_iff o).mpr hK, fun i h0 => hne i ?_⟩
  exact o.injective (h0.trans (map_bot o).symm)

/-- The uniform dimension is invariant under linear equivalences. -/
theorem uniformDimGE_congr {N : Type w} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    {n : ℕ} : UniformDimGE R M n ↔ UniformDimGE R N n :=
  ⟨UniformDimGE.of_linearEquiv e, UniformDimGE.of_linearEquiv e.symm⟩

/-- **Uniform dimension is bounded by length.** If `M` contains a direct sum of
`n` nonzero submodules, then `n ≤ length M`: the direct sum embeds into `M`, and
each summand has length at least one. -/
theorem UniformDimGE.le_length {n : ℕ} (h : UniformDimGE R M n) :
    (n : ℕ∞) ≤ Module.length R M := by
  classical
  obtain ⟨N, hN, hne⟩ := h
  calc (n : ℕ∞) = ∑ _i : Fin n, (1 : ℕ∞) := by simp
    _ ≤ ∑ i, Module.length R (N i) := Finset.sum_le_sum fun i _ => by
        have := (Submodule.nontrivial_iff_ne_bot).mpr (hne i)
        exact Order.one_le_iff_pos.mpr Module.length_pos
    _ = Module.length R (Π i, N i) := (Module.length_pi_of_fintype R _).symm
    _ = Module.length R (Π₀ i, N i) := (DFinsupp.linearEquivFunOnFintype).length_eq.symm
    _ ≤ Module.length R M := Module.length_le_of_injective _ hN.dfinsupp_lsum_injective

/-- If `length M ≤ n`, then `M` contains no direct sum of `n + 1` nonzero
submodules. -/
theorem uniformDimLE_of_length_le {n : ℕ} (h : Module.length R M ≤ n) :
    UniformDimLE R M n := fun hge => by
  have := hge.le_length.trans h
  norm_cast at this
  omega

/-- **Uniform dimension of a semisimple module.** A semisimple module contains a
direct sum of `n` nonzero submodules if and only if its length is at least `n`. -/
theorem uniformDimGE_iff_le_length [IsSemisimpleModule R M] {n : ℕ} :
    UniformDimGE R M n ↔ (n : ℕ∞) ≤ Module.length R M := by
  classical
  refine ⟨UniformDimGE.le_length, fun hn => ?_⟩
  obtain ⟨s, e, hs, hsimple⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R M
  have hind : iSupIndep fun m : s => m.1 := (sSupIndep_iff s).mp hs
  have hne : ∀ m : s, m.1 ≠ ⊥ := fun m =>
    (Submodule.nontrivial_iff_ne_bot).mp (IsSimpleModule.nontrivial R m.1)
  suffices hemb : Nonempty (Fin n ↪ s) by
    obtain ⟨f⟩ := hemb
    exact ⟨fun i => (f i).1, hind.comp f.injective, fun i => hne _⟩
  rcases finite_or_infinite s with hfin | hinf
  · cases nonempty_fintype s
    have hlen : Module.length R M = Fintype.card s := by
      rw [e.length_eq, (DFinsupp.linearEquivFunOnFintype).length_eq,
        Module.length_pi_of_fintype]
      simp
    rw [hlen] at hn
    norm_cast at hn
    exact ⟨(Fin.castLEEmb hn).trans (Fintype.equivFin s).symm.toEmbedding⟩
  · exact ⟨(Fin.valEmbedding.trans (Infinite.natEmbedding s))⟩

/-- **Uniform dimension of a semisimple module.** A semisimple module contains no
direct sum of `n + 1` nonzero submodules if and only if its length is at most
`n`. -/
theorem uniformDimLE_iff_length_le [IsSemisimpleModule R M] {n : ℕ} :
    UniformDimLE R M n ↔ Module.length R M ≤ n := by
  rw [UniformDimLE, uniformDimGE_iff_le_length, not_le, Nat.cast_add, Nat.cast_one,
    ENat.lt_add_one_iff (ENat.natCast_ne_top n)]

end AlgebraicAnalysis.Module
