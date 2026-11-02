module

public import AlgebraicAnalysis.RingTheory.Goldie.Basic
public import AlgebraicAnalysis.Ore.RightLocalization

@[expose] public section

/-!
# Goldie's theorem: the quotient ring of a simple right Noetherian ring

Let `R` be a simple right Noetherian ring. By `Goldie.exists_right_ore` its
regular elements form a right Ore set, so `R` has a classical right quotient
ring `Q`, whose elements are right fractions `r s⁻¹` with `s` regular. Goldie's
theorem says that `Q` is a simple Artinian ring; by the Wedderburn–Artin
theorem it is a matrix ring `Mₙ(D)` over a division ring `D`.

Mathlib's `OreLocalization` builds left fractions `s⁻¹ r`. As in
`AlgebraicAnalysis.OreRightLocalization.RightOreLocalization`, we form the Ore
localization `Q°` of the opposite ring `Rᵐᵒᵖ` at the opposite copy of `R⁰`
(`Goldie.OppositeQuotientRing R`) and set `Q = (Q°)ᵐᵒᵖ`
(`Goldie.QuotientRing R`, definitionally `RightOreLocalization R R⁰`). Left
ideals of `Q°` are right ideals of `Q`; simplicity and semisimplicity pass
between a ring and its opposite (Mathlib instances).

The Ore set structure is data, so the results below take an instance
`[OreLocalization.OreSet (oppositeSubmonoid R⁰)]`;
`Goldie.nonempty_oreSet_oppositeSubmonoid` shows that one exists. (Different
choices give isomorphic rings by the universal property; this is not used.)

## Main results

* `Goldie.isSimpleRing_quotientRing`: `Q` is a simple ring;
* `Goldie.isSemisimpleRing_quotientRing`, `Goldie.isArtinianRing_quotientRing`,
  `Goldie.isArtinianRing_oppositeQuotientRing`: `Q` is semisimple, and left and
  right Artinian;
* `Goldie.exists_ringEquiv_matrix_divisionRing`: `Q ≃ Mₙ(D)` for some `n ≠ 0`
  and division ring `D`;
* `Goldie.length_oppositeQuotientRing_ne_top`,
  `Goldie.length_oppositeQuotientRing_pos`: `Q` has finite positive length as a
  right module over itself;
* `Goldie.toQuotientRing`: the canonical ring map `R → Q`, injective and
  sending regular elements to units.

## Proof

Write `ι : R → Q` for the canonical map; every `q ∈ Q` has the form
`q = ι(r) ι(t)⁻¹` with `t` regular, `ι` is injective, and `ι(t)` is a unit for
regular `t`.

*Every essential right ideal `E` of `Q` is `Q`.* The right ideal
`J = ι⁻¹(E)` of `R` is essential: for `y ≠ 0`, `ι(y) Q` meets `E` in some
`ι(y) q ≠ 0`; writing `q = ι(r) ι(t)⁻¹` gives `ι(y r) = ι(y) q ι(t) ∈ E`, and
`y r ≠ 0`. By Goldie (`exists_mem_nonZeroDivisors_of_isEssential`) `J`
contains a regular `s`, and `ι(s) ∈ E` is a unit.

*`Q` is semisimple.* For a right ideal `L` of `Q` choose, by Zorn's lemma, a
right ideal `L'` maximal with `L ∩ L' = 0`. Then `L + L'` is essential: if
`N ∩ (L + L') = 0`, the modular law gives `L ∩ (L' + N) = 0`, so `N ≤ L'` by
maximality and `N = 0`. Hence `L + L' = Q` and `L'` is a complement of `L`.

*`Q` is simple.* A nonzero two-sided ideal `T` of `Q` contains some
`q = ι(r) ι(t)⁻¹ ≠ 0`, hence `ι(r) = q ι(t) ≠ 0`; then `ι⁻¹(T)` is a nonzero
two-sided ideal of the simple ring `R`, so `1 ∈ T`.

A simple semisimple ring is Artinian, and Wedderburn–Artin applies
(`IsSimpleRing.exists_ringEquiv_matrix_divisionRing`).

## References

A. W. Goldie, *The structure of prime rings under ascending chain
conditions*, Proc. London Math. Soc. (3) 8 (1958) 589–608; *Semi-prime rings
with maximum condition*, ibid. 10 (1960) 201–220; J. C. McConnell and
J. C. Robson, *Noncommutative Noetherian Rings*, 2.3.6 and 2.3.10. Nothing
here is new.
-/

namespace AlgebraicAnalysis.Goldie

open MulOpposite nonZeroDivisors OreLocalization OreRightLocalization

universe u

theorem mem_oppositeSubmonoid_nonZeroDivisors {R : Type u} [Ring R] {x : Rᵐᵒᵖ} :
    x ∈ oppositeSubmonoid R⁰ ↔ x ∈ (Rᵐᵒᵖ)⁰ := by
  rw [← op_unop x, op_mem_nonZeroDivisors_iff]
  exact Iff.rfl

/-- **Goldie (right Ore condition).** The opposite copy of the regular
elements of a simple right Noetherian ring is an Ore set of `Rᵐᵒᵖ` in
Mathlib's convention. -/
theorem nonempty_oreSet_oppositeSubmonoid {R : Type u} [Ring R] [IsSimpleRing R]
    [IsNoetherian Rᵐᵒᵖ R] : Nonempty (OreLocalization.OreSet (oppositeSubmonoid R⁰)) := by
  refine OreLocalization.nonempty_oreSet_iff.mpr ⟨?_, ?_⟩
  · rintro r₁ r₂ ⟨s, hs⟩ he
    refine ⟨1, ?_⟩
    have hs' : unop s ∈ R⁰ := hs
    have h : unop s * (unop r₁ - unop r₂) = 0 := by
      rw [mul_sub, sub_eq_zero]
      exact congrArg unop he
    rw [unop_injective (sub_eq_zero.mp (hs'.1 _ h))]
  · rintro r ⟨s, hs⟩
    obtain ⟨a', s', hs', he⟩ := exists_right_ore (unop r) (show unop s ∈ R⁰ from hs)
    exact ⟨op a', ⟨op s', hs'⟩, unop_injective he⟩

variable (R : Type u) [Ring R] [OreLocalization.OreSet (oppositeSubmonoid R⁰)]

/-- The Ore localization of the opposite ring `Rᵐᵒᵖ` at the opposite copy of
the regular elements, made of left fractions `s⁻¹ r` in `Rᵐᵒᵖ`. Its opposite is
the classical right quotient ring `Goldie.QuotientRing R`. -/
abbrev OppositeQuotientRing : Type u := OreLocalization (oppositeSubmonoid R⁰) Rᵐᵒᵖ

/-- The classical right quotient ring `Q` of `R`: the ring of right fractions
`r s⁻¹` with `s` regular. -/
abbrev QuotientRing : Type u := RightOreLocalization R R⁰

/-- The canonical ring map `ι : R → Q`, `r ↦ r 1⁻¹`. -/
abbrev toQuotientRing : R →+* QuotientRing R := rightNumeratorRingHom (S := R⁰)

variable {R}

theorem toQuotientRing_apply (r : R) :
    toQuotientRing R r = op (numeratorRingHom (S := oppositeSubmonoid R⁰) (op r)) := rfl

section Basic

/-- Every element of `Q°` becomes a numerator after left multiplication by a
regular numerator: `t q = r` for some regular `t`. -/
theorem exists_numerator_mul_eq (q : OppositeQuotientRing R) :
    ∃ t ∈ oppositeSubmonoid R⁰, ∃ r : Rᵐᵒᵖ, numeratorRingHom (S := oppositeSubmonoid R⁰) t * q =
      numeratorRingHom r := by
  induction q using OreLocalization.ind with
  | _ r s =>
    refine ⟨s, s.2, r, ?_⟩
    change ((s : Rᵐᵒᵖ) /ₒ (1 : oppositeSubmonoid R⁰)) * (r /ₒ s) = r /ₒ 1
    exact OreLocalization.mul_cancel

theorem numeratorRingHom_injective :
    Function.Injective (numeratorRingHom (R := Rᵐᵒᵖ) (S := oppositeSubmonoid R⁰)) :=
  numeratorHom_inj fun _ hx => (mem_oppositeSubmonoid_nonZeroDivisors.mp hx).1

theorem isUnit_numeratorRingHom {s : Rᵐᵒᵖ} (hs : s ∈ oppositeSubmonoid R⁰) :
    IsUnit (numeratorRingHom (S := oppositeSubmonoid R⁰) s) :=
  numerator_isUnit ⟨s, hs⟩

/-- The canonical map `R → Q` is injective. -/
theorem toQuotientRing_injective : Function.Injective (toQuotientRing R) := fun _ _ h =>
  op_injective (numeratorRingHom_injective (op_injective h))

/-- Regular elements of `R` become units in `Q`. -/
theorem isUnit_toQuotientRing {s : R} (hs : s ∈ R⁰) : IsUnit (toQuotientRing R s) :=
  (isUnit_numeratorRingHom (s := op s) hs).op

end Basic

variable [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]

/-- In `Q°`, a left ideal meeting every nonzero left ideal is everything (in `Q`:
every essential right ideal is `Q`). -/
theorem eq_top_of_forall_inf_eq_bot (E : Submodule (OppositeQuotientRing R)
    (OppositeQuotientRing R)) (hE : ∀ N, N ⊓ E = ⊥ → N = ⊥) : E = ⊤ := by
  let ι := numeratorRingHom (R := Rᵐᵒᵖ) (S := oppositeSubmonoid R⁰)
  let J : Submodule Rᵐᵒᵖ R :=
    { carrier := {r | ι (op r) ∈ E}
      add_mem' := fun {x y} hx hy => by
        change ι (op (x + y)) ∈ E
        rw [op_add, map_add]
        exact E.add_mem hx hy
      zero_mem' := by
        change ι (op 0) ∈ E
        rw [op_zero, map_zero]
        exact E.zero_mem
      smul_mem' := fun c x hx => by
        change ι (op (x * unop c)) ∈ E
        rw [op_mul, op_unop, map_mul]
        exact E.smul_mem (ι c) hx }
  have hJ : IsEssential J := by
    intro y hy
    have hq0 : ι (op y) ≠ 0 := fun h =>
      hy (op_injective (numeratorRingHom_injective (h.trans (map_zero ι).symm)))
    have hspan : Submodule.span _ {ι (op y)} ⊓ E ≠ ⊥ := fun h =>
      hq0 (Submodule.span_singleton_eq_bot.mp (hE _ h))
    obtain ⟨z, ⟨hzspan, hzE⟩, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hspan
    obtain ⟨q, rfl⟩ := Submodule.mem_span_singleton.mp hzspan
    obtain ⟨t, ht, r, hr⟩ := exists_numerator_mul_eq q
    have key : ι (op (y * unop r)) = ι t * (q • ι (op y)) := by
      rw [op_mul, op_unop, map_mul, ← hr, smul_eq_mul, mul_assoc]
    refine ⟨unop r, fun h0 => hz0 ?_, ?_⟩
    · have h1 : ι t * (q • ι (op y)) = 0 := by rw [← key, h0, op_zero, map_zero]
      exact (isUnit_numeratorRingHom ht).mul_right_eq_zero.mp h1
    · change ι (op (y * unop r)) ∈ E
      rw [key]
      exact E.smul_mem (ι t) hzE
  obtain ⟨s, hsJ, hs⟩ := exists_mem_nonZeroDivisors_of_isEssential hJ
  exact Ideal.eq_top_of_isUnit_mem E hsJ
    (isUnit_numeratorRingHom (s := op s) hs)

/-- Every left ideal of `Q°` has a complement (in `Q`: every right ideal is a
direct summand). -/
theorem exists_isCompl (L : Submodule (OppositeQuotientRing R) (OppositeQuotientRing R)) :
    ∃ L', IsCompl L L' := by
  obtain ⟨L', hL', hmax⟩ := zorn_le₀ {N | Disjoint L N} fun c hc hchain =>
    ⟨sSup c, hchain.directedOn.disjoint_sSup_right.mpr fun _ hb => hc hb,
      fun _ hz => le_sSup hz⟩
  refine ⟨L', hL', codisjoint_iff.mpr (eq_top_of_forall_inf_eq_bot _ fun N hN => ?_)⟩
  have hdisj : Disjoint (L ⊔ L') N := disjoint_iff.mpr (by rw [inf_comm, hN])
  have hle : L' ⊔ N ≤ L' :=
    hmax (Disjoint.disjoint_sup_right_of_disjoint_sup_left hL' hdisj) le_sup_left
  have hNL : N ≤ L ⊔ L' := (le_sup_right.trans hle).trans le_sup_right
  rw [← hN, inf_eq_left.mpr hNL]

instance isSemisimpleRing_oppositeQuotientRing :
    IsSemisimpleRing (OppositeQuotientRing R) :=
  have : ComplementedLattice (Submodule (OppositeQuotientRing R) (OppositeQuotientRing R)) :=
    ⟨exists_isCompl⟩
  ⟨⟩

instance isSimpleRing_oppositeQuotientRing : IsSimpleRing (OppositeQuotientRing R) := by
  have : Nontrivial (OppositeQuotientRing R) :=
    OreLocalization.nontrivial_of_nonZeroDivisors fun _ hx =>
      mem_oppositeSubmonoid_nonZeroDivisors.mp hx
  refine IsSimpleRing.of_eq_bot_or_eq_top fun T => or_iff_not_imp_left.mpr fun hT => ?_
  let ι := numeratorRingHom (R := Rᵐᵒᵖ) (S := oppositeSubmonoid R⁰)
  obtain ⟨z, hzT, hz0⟩ : ∃ z ∈ T, z ≠ 0 := by
    by_contra! h
    exact hT (TwoSidedIdeal.ext fun x => ⟨fun hx => by simp [h x hx], fun hx => by
      rw [(TwoSidedIdeal.mem_bot _).mp hx]; exact T.zero_mem⟩)
  obtain ⟨t, ht, r, hr⟩ := exists_numerator_mul_eq z
  have hrT : r ∈ T.comap ι := by
    rw [TwoSidedIdeal.mem_comap, ← hr]
    exact T.mul_mem_left _ _ hzT
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hr
    exact hz0 ((isUnit_numeratorRingHom ht).mul_right_eq_zero.mp hr)
  have h1 := IsSimpleRing.one_mem_of_ne_zero_mem _ hr0 hrT
  rw [TwoSidedIdeal.mem_comap, map_one] at h1
  exact (TwoSidedIdeal.one_mem_iff T).mp h1

/-- **Goldie's theorem.** The classical right quotient ring of a simple right
Noetherian ring is simple. -/
instance isSimpleRing_quotientRing : IsSimpleRing (QuotientRing R) := inferInstance

/-- **Goldie's theorem.** The classical right quotient ring of a simple right
Noetherian ring is semisimple. -/
instance isSemisimpleRing_quotientRing : IsSemisimpleRing (QuotientRing R) := inferInstance

/-- **Goldie's theorem.** The classical right quotient ring of a simple right
Noetherian ring is Artinian (as a left module over itself; it is also right
Artinian, `isArtinianRing_oppositeQuotientRing`). -/
instance isArtinianRing_quotientRing : IsArtinianRing (QuotientRing R) :=
  IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mp inferInstance

instance isArtinianRing_oppositeQuotientRing : IsArtinianRing (OppositeQuotientRing R) :=
  IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mp inferInstance

/-- The length of `Q` as a right module over itself, which is the length of `Q°`
as a left module over itself, is finite. Together with
`length_oppositeQuotientRing_pos` this makes the normalized rank
`length_Q(N) / length_Q(Q)` of a right `Q`-module of finite length well defined. -/
theorem length_oppositeQuotientRing_ne_top :
    Module.length (OppositeQuotientRing R) (OppositeQuotientRing R) ≠ ⊤ :=
  Module.length_ne_top

omit [IsNoetherian Rᵐᵒᵖ R] in
/-- The length of `Q` as a right module over itself is positive. -/
theorem length_oppositeQuotientRing_pos :
    0 < Module.length (OppositeQuotientRing R) (OppositeQuotientRing R) :=
  Module.length_pos

/-- **Goldie's theorem with Wedderburn–Artin.** The classical right quotient
ring of a simple right Noetherian ring is a matrix ring `Mₙ(D)`, `n ≠ 0`, over
a division ring `D`. -/
theorem exists_ringEquiv_matrix_divisionRing :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D),
      Nonempty (QuotientRing R ≃+* Matrix (Fin n) (Fin n) D) :=
  IsSimpleRing.exists_ringEquiv_matrix_divisionRing (QuotientRing R)

end AlgebraicAnalysis.Goldie
