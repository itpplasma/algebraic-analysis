module
public import AlgebraicAnalysis.DifferentialOperators.CoordinateSymbol
public import AlgebraicAnalysis.RingTheory.InfiniteCenter
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section

/-!
# Simplicity of `D_k(R)`

Call an ideal `J` of the nontrivial commutative `k`-algebra `R`
**differential** if `D J ⊆ J` for every `k`-derivation `D` of `R`. If the only
nonzero differential ideal of `R` is `R` itself, then `D_k(R)` is a simple
ring (`isSimpleRing_of_derivation`). No coordinates and no characteristic
assumption are needed.

## Proof

Let `I` be a nonzero two-sided ideal of `D = D_k(R)` and `P ∈ I` nonzero of
minimal order. The commutators `[P, a] = P a - a P` (`a ∈ R`) lie in `I` and
have smaller order, so they vanish, and `P` is multiplication by some `f ≠ 0`
(`exists_multiplication_mem`). The multipliers `J = {f ∈ R | f ∈ I}` form a
nonzero ideal of `R`, which is differential because `[D, f] = D(f)`. Hence
`J = R`, `1 ∈ I` and `I = D`.

In characteristic zero the hypothesis holds for polynomial rings and their
localizations (`LocalizedPolynomialOperators`) and for smooth domains
(`SmoothSimplicity`). The argument is AA-native; compare [McConnell–Robson,
*Noncommutative Noetherian Rings*, 15.3.8] and [Coutinho, *A Primer of
Algebraic D-modules*, 2.2.1].

`DifferentialOperators.infinite_center`: over an infinite field (in particular
in characteristic zero), `D_k(R)` has infinite centre.
-/

namespace AlgebraicAnalysis.DifferentialOperators

section Criterion

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- **A nonzero two-sided ideal of `D_k(R)` contains a nonzero multiplication.**
Induction on the order: if all `[P, a]` vanish, `P` is a multiplication;
otherwise some `[P, a] ∈ I` is nonzero of smaller order. No coordinates are
needed. -/
theorem exists_multiplication_mem (I : TwoSidedIdeal (algebra (k := k) (R := R))) :
    ∀ m, ∀ P ∈ I, P ≠ 0 → (P : End (k := k) (R := R)) ∈ order m →
      ∃ f : R, f ≠ 0 ∧ multiplicationAlgHom k R f ∈ I := by
  intro m
  induction m with
  | zero =>
      intro P hPI hP0 hP
      have hPf : multiplicationAlgHom k R (P.1 1) = P :=
        Subtype.ext ((mem_order_zero_iff_eq_multiplication _).mp hP).symm
      refine ⟨P.1 1, fun h => hP0 ?_, by rw [hPf]; exact hPI⟩
      rw [← hPf, h, map_zero]
  | succ m ih =>
      intro P hPI hP0 hP
      by_cases hcomm : ∀ a, P * multiplicationAlgHom k R a -
          multiplicationAlgHom k R a * P = 0
      · exact ih P hPI hP0 (order_mono (Nat.zero_le m) fun a => congrArg Subtype.val (hcomm a))
      · push Not at hcomm
        obtain ⟨a, ha⟩ := hcomm
        exact ih _ (I.sub_mem (I.mul_mem_right _ _ hPI) (I.mul_mem_left _ _ hPI)) ha
          ((mem_order_succ_iff _ m).mp hP a)

/-- **Simplicity criterion.** `D_k(R)` is simple if `R` is nontrivial and has
no nonzero proper ideal stable under all `k`-derivations. -/
theorem isSimpleRing_of_derivation [Nontrivial R]
    (hR : ∀ J : Ideal R, J ≠ ⊥ → (∀ D : Derivation k R R, ∀ f ∈ J, D f ∈ J) → J = ⊤) :
    IsSimpleRing (algebra (k := k) (R := R)) := by
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  obtain ⟨P, hPI, hP0⟩ : ∃ P ∈ I, P ≠ 0 := by
    by_contra h
    push Not at h
    exact hI (eq_bot_iff.mpr fun P hP => (TwoSidedIdeal.mem_bot _).mpr (h P hP))
  obtain ⟨m, hm⟩ := P.2
  obtain ⟨f, hf0, hfI⟩ := exists_multiplication_mem I m P hPI hP0 hm
  let J : Ideal R :=
    { carrier := {g | multiplicationAlgHom k R g ∈ I}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        exact I.add_mem ha hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact I.zero_mem
      smul_mem' := fun c g hg => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at hg ⊢
        exact I.mul_mem_left _ _ hg }
  have hJ : J = ⊤ := by
    refine hR J (fun h => hf0 ?_) (fun D g hg => ?_)
    · have hfJ : f ∈ J := hfI
      rwa [h, Ideal.mem_bot] at hfJ
    · have hD : multiplicationAlgHom k R (D g) =
          derivationElem D * multiplicationAlgHom k R g -
            multiplicationAlgHom k R g * derivationElem D :=
        Subtype.ext (commutator_derivation D g).symm
      change multiplicationAlgHom k R (D g) ∈ I
      rw [hD]
      exact I.sub_mem (I.mul_mem_left _ _ hg) (I.mul_mem_right _ _ hg)
  have h1 : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
  have h1' : multiplicationAlgHom k R 1 ∈ I := h1
  rw [map_one] at h1'
  exact (TwoSidedIdeal.one_mem_iff I).mp h1'

end Criterion

/-- **`D_k(R)` has an infinite centre** over an infinite field: it contains the
scalars. -/
theorem infinite_center (k R : Type*) [Field k] [Infinite k] [CommRing R] [Nontrivial R]
    [Algebra k R] : Infinite (Subring.center (algebra (k := k) (R := R))) :=
  infinite_subring_center k _

end AlgebraicAnalysis.DifferentialOperators
