module

public import AlgebraicAnalysis.RingTheory.Goldie.Rank
public import Mathlib.Algebra.DirectSum.Idempotents

@[expose] public section

/-!
# Idempotents of the quotient ring with common denominators

Let `R` be a simple right Noetherian ring with classical right quotient ring
`Q`, and let `s = length_Q(Q_Q) = goldieRank R R`. Since `Q` is semisimple,
`Q_Q` is a direct sum of `s` simple right ideals, and the decomposition
`1 = E₁ + ⋯ + E_s` gives complete orthogonal idempotents with `Eᵢ Q` simple.
Clearing denominators in `R` gives the device used for upper bounds on the
number of generators of a module:

* a regular `c ∈ R` with `fᵢ = Eᵢ c ∈ R` for all `i`;
* regular `tᵢ ∈ R` with `rᵢ = c⁻¹ Eᵢ tᵢ ∈ R`, stated without inverses as
  `c rᵢ = Eᵢ tᵢ` in `Q`.

Then `fᵢ rⱼ = 0` for `i ≠ j`, and `eᵢ = fᵢ rᵢ = Eᵢ tᵢ ≠ 0`
(`Goldie.exists_idempotent_denominators`).

As elsewhere, `Q = (Q°)ᵐᵒᵖ` with `Q° = OppositeQuotientRing R`; the right ideal
`Eᵢ Q` of `Q` is the left ideal `Q° · unop Eᵢ` of `Q°`, and its simplicity is
stated for that left ideal.

## References

J. C. McConnell and J. C. Robson, *Noncommutative Noetherian Rings*, 2.1.3 and
2.3.6; T. Y. Lam, *A First Course in Noncommutative Rings*, §3 and §21
(idempotents attached to a direct sum decomposition). Nothing here is new.
-/

namespace AlgebraicAnalysis.Goldie

open MulOpposite nonZeroDivisors OreRightLocalization

universe u

variable {R : Type u} [Ring R] [OreLocalization.OreSet (oppositeSubmonoid R⁰)]

section Decomposition

variable [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]

/-- `Q°` is a direct sum of `n = length(Q°)` simple left ideals `Q° eᵢ`, given by
complete orthogonal idempotents `eᵢ`. -/
theorem exists_completeOrthogonalIdempotents_oppositeQuotientRing :
    ∃ (n : ℕ) (e : Fin n → OppositeQuotientRing R),
      (n : ℕ∞) = Module.length (OppositeQuotientRing R) (OppositeQuotientRing R) ∧
      CompleteOrthogonalIdempotents e ∧
      ∀ i, IsSimpleModule (OppositeQuotientRing R)
        (Submodule.span (OppositeQuotientRing R) {e i}) := by
  classical
  set Q := OppositeQuotientRing R
  obtain ⟨s, hind, hsup, hsimple⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top Q Q
  have hind' : iSupIndep fun m : s => m.1 := (sSupIndep_iff s).mp hind
  have hfin : Finite s := WellFoundedGT.finite_of_iSupIndep hind'
    fun m => have := hsimple _ m.2
      (Submodule.nontrivial_iff_ne_bot).mp (IsSimpleModule.nontrivial Q m.1)
  let eq := Finite.equivFin s
  let V : Fin (Nat.card s) → Ideal Q := fun i => (eq.symm i).1
  have hV : iSupIndep V := hind'.comp eq.symm.injective
  have hVsup : iSup V = ⊤ := by
    rw [← hsup, sSup_eq_iSup']
    exact eq.symm.iSup_comp (g := fun m : s => m.1)
  have hint : DirectSum.IsInternal V :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hV hVsup
  let := hint.chooseDecomposition
  have hsimpleV : ∀ i, IsSimpleModule Q (V i) := fun i => hsimple _ (eq.symm i).2
  have hspan : ∀ i, Submodule.span Q {DirectSum.idempotent V i} = V i := by
    intro i
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact (DirectSum.decompose V (1 : Q) i).2
    · intro x hx
      rw [← DirectSum.decompose_of_mem_same V hx, DirectSum.decompose_eq_mul_idempotent]
      exact Submodule.smul_mem _ x (Submodule.subset_span rfl)
  refine ⟨Nat.card s, DirectSum.idempotent V, ?_,
    DirectSum.completeOrthogonalIdempotents_idempotent V, fun i => by rw [hspan]; exact hsimpleV i⟩
  have e := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hint
  rw [← e.length_eq, (DFinsupp.linearEquivFunOnFintype).length_eq, Module.length_pi_of_fintype]
  rw [Finset.sum_congr rfl fun i _ => Module.length_eq_one_iff.mpr (hsimpleV i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_one]

end Decomposition

/-- **Idempotents with common denominators** (the device of McConnell–Robson 2.3.6
used for generator bounds). Let `R` be simple and right Noetherian with
classical right quotient ring `Q` and `ι : R → Q`. There are `n = rk(R_R) =
length_Q(Q_Q)` complete orthogonal idempotents `E₁, …, E_n` of `Q` with each
`Eᵢ Q` simple, a regular `c`, regular `tᵢ` and elements `fᵢ, rᵢ` of `R` with

* `Eᵢ c = fᵢ` and `c rᵢ = Eᵢ tᵢ` in `Q` (so `rᵢ = c⁻¹ Eᵢ tᵢ`);
* `fᵢ rⱼ = 0` for `i ≠ j`;
* `fᵢ rᵢ = Eᵢ tᵢ` in `Q`, and `fᵢ rᵢ ≠ 0`. -/
theorem exists_idempotent_denominators [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] :
    ∃ (n : ℕ) (E : Fin n → QuotientRing R) (c : R) (t f r : Fin n → R),
      (n : ℕ∞) = goldieRank R R ∧
      CompleteOrthogonalIdempotents E ∧
      (∀ i, IsSimpleModule (OppositeQuotientRing R)
        (Submodule.span (OppositeQuotientRing R) {unop (E i)})) ∧
      c ∈ R⁰ ∧ (∀ i, t i ∈ R⁰) ∧
      (∀ i, E i * toQuotientRing R c = toQuotientRing R (f i)) ∧
      (∀ i, toQuotientRing R c * toQuotientRing R (r i) = E i * toQuotientRing R (t i)) ∧
      (∀ i j, i ≠ j → f i * r j = 0) ∧
      (∀ i, toQuotientRing R (f i * r i) = E i * toQuotientRing R (t i)) ∧
      (∀ i, f i * r i ≠ 0) := by
  classical
  let ι := toQuotientRing R
  obtain ⟨n, e, hn, he, hsimple⟩ := exists_completeOrthogonalIdempotents_oppositeQuotientRing
    (R := R)
  let E : Fin n → QuotientRing R := fun i => op (e i)
  have hE : CompleteOrthogonalIdempotents E := by
    refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
    · change op (e i) * op (e i) = op (e i)
      rw [← op_mul, he.idem i]
    · change op (e i) * op (e j) = 0
      rw [← op_mul, he.ortho (Ne.symm hij), op_zero]
    · change ∑ i, opAddEquiv (e i) = 1
      rw [← map_sum, he.complete]
      rfl
  have hE0 : ∀ i, E i ≠ 0 := by
    intro i h0
    have h2 : e i = 0 := op_injective h0
    have h := (hsimple i).nontrivial
    rw [h2] at h
    exact (Submodule.nontrivial_iff_ne_bot.mp h) (by simp)
  -- the right ideal of denominators clearing `E i`
  let J : Fin n → Submodule Rᵐᵒᵖ R := fun i =>
    { carrier := {x | ∃ a, E i * ι x = ι a}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by rw [map_add, mul_add, ha, hb, map_add]⟩
      zero_mem' := ⟨0, by rw [map_zero, mul_zero]⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        refine ⟨a * unop c, ?_⟩
        change E i * ι (x * unop c) = ι (a * unop c)
        rw [map_mul, ← mul_assoc, ha, map_mul] }
  obtain ⟨c, hc, hcJ⟩ := exists_mem_nonZeroDivisors_finset Finset.univ J fun i _ => by
    obtain ⟨a, s, hs, -, hsa⟩ := rightOre_clear (S := R⁰) (E i)
    exact ⟨s, ⟨a, hsa⟩, hs⟩
  choose f hf using fun i => hcJ i (Finset.mem_univ i)
  have hcu := isUnit_toQuotientRing hc
  have hrt : ∀ i, ∃ r t : R, t ∈ R⁰ ∧ ι c * ι r = E i * ι t := by
    intro i
    obtain ⟨a, t, ht, -, hta⟩ := rightOre_clear (S := R⁰) (↑hcu.unit⁻¹ * E i)
    refine ⟨a, t, ht, ?_⟩
    rw [← hta, ← mul_assoc, ← mul_assoc]
    change ↑hcu.unit * ↑hcu.unit⁻¹ * E i * ι t = E i * ι t
    rw [Units.mul_inv, one_mul]
  choose r t ht hrt using hrt
  have hfr : ∀ i j, ι (f i * r j) = E i * E j * ι (t j) := by
    intro i j
    rw [map_mul, ← hf i, mul_assoc, hrt j, mul_assoc]
  refine ⟨n, E, c, t, f, r, hn.trans (goldieRank_self R).symm, hE, hsimple, hc, ht, hf, hrt,
    fun i j hij => ?_, fun i => ?_, fun i h0 => ?_⟩
  · apply toQuotientRing_injective
    change ι (f i * r j) = ι 0
    rw [hfr, hE.ortho hij, zero_mul, map_zero]
  · rw [hfr, (hE.idem i).eq]
  · have h1 : E i * ι (t i) = 0 := by
      rw [← (hE.idem i).eq, ← hfr]
      rw [h0, map_zero]
    exact hE0 i ((isUnit_toQuotientRing (ht i)).mul_left_eq_zero.mp h1)

end AlgebraicAnalysis.Goldie
