module

public import AlgebraicAnalysis.RingTheory.Goldie.Rank
public import AlgebraicAnalysis.RingTheory.SimpleArtinian

@[expose] public section

/-!
# Free cyclic submodules and spanning fractions

Let `R` be a simple right Noetherian ring with classical right quotient ring
`Q`, and let `M` be a finitely generated right `R`-module with module of
fractions `M_Q` (`Goldie.FractionModule R M`) and Goldie rank
`rk(M) = length_Q(M_Q)`. Write `s = rk(R_R) = length_Q(Q_Q)`.

* `Goldie.eq_top_of_forall_toFractionModule_smul_mem` (`R` simple, no
  Noetherian hypothesis): a `Q`-submodule of `M_Q` that contains the fraction of
  `m e` for every `m ∈ M` and one fixed `e ≠ 0` is all of `M_Q`.
* `Goldie.exists_injective_toSpanSingleton`: if `s ≤ rk(M)`, some `p ∈ M` has
  zero annihilator, so `pR ≅ R_R`.
* `Goldie.exists_goldieRank_eq_add_quotient`: if `s ≤ rk(M)`, some `p ∈ M`
  satisfies `rk(M) = s + rk(M/pR)`.
* `Goldie.exists_span_fraction_eq_top`: for nonzero `e₀, …, e_{n-1}` and
  `rk(M) = l < n` there are `m_j ∈ M`, zero for `j ≥ l`, such that the fractions
  of the `m_j e_j` span `M_Q`.

## References

J. C. McConnell and J. C. Robson, *Noncommutative Noetherian Rings*, 2.3.6 and
2.2.10–2.2.13 (Goldie's theorem, modules of fractions); T. Y. Lam, *A First
Course in Noncommutative Rings*, §3. Nothing here is new.
-/

namespace AlgebraicAnalysis.Goldie

open MulOpposite nonZeroDivisors OreRightLocalization

universe u v

variable {R : Type u} [Ring R] [OreLocalization.OreSet (oppositeSubmonoid R⁰)]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- **Simplicity argument.** Let `R` be simple, `e ≠ 0` and `U` a
`Q`-submodule of `M_Q` containing the fraction of `m e` for every `m ∈ M`. Then
`U = M_Q`: the `r` with `M r ⊆ U` form a two-sided ideal containing `e`, hence
`1`, and every fraction `m c⁻¹` lies in `U`. -/
theorem eq_top_of_forall_toFractionModule_smul_mem [IsSimpleRing R] {e : R} (he : e ≠ 0)
    (U : Submodule (OppositeQuotientRing R) (FractionModule R M))
    (hU : ∀ m : M, toFractionModule R M (op e • m) ∈ U) : U = ⊤ := by
  -- the two-sided ideal of all `r` with `toFrac(m r) ∈ U` for every `m`
  let J : TwoSidedIdeal R :=
    TwoSidedIdeal.mk' {r | ∀ m : M, toFractionModule R M (op r • m) ∈ U}
    (fun m => by simp)
    (fun hx hy m => by rw [op_add, add_smul, map_add]; exact U.add_mem (hx m) (hy m))
    (fun hx m => by rw [op_neg, neg_smul, map_neg]; exact U.neg_mem (hx m))
    (fun {x y} hy m => by rw [op_mul, mul_smul]; exact hy _)
    (fun {x y} hx m => by
      rw [op_mul, mul_smul, map_smul,
        ← OreModule.oreDiv_one_smul_eq (S := oppositeSubmonoid R⁰)]
      exact U.smul_mem _ (hx m))
  have h1 : (1 : R) ∈ J :=
    IsSimpleRing.one_mem_of_ne_zero_mem J he ((TwoSidedIdeal.mem_mk' ..).mpr hU)
  rw [eq_top_iff]
  intro x _
  induction x using OreLocalization.ind with | _ m c =>
  have hx : m /ₒ c = ((1 : Rᵐᵒᵖ) /ₒ c) • toFractionModule R M m := by
    rw [OreModule.toLocalization_apply, OreLocalization.one_div_smul, one_mul]
  rw [hx]
  refine U.smul_mem _ ?_
  simpa using (TwoSidedIdeal.mem_mk' ..).mp h1 m

/-- **A free cyclic submodule.** If `R` is simple right Noetherian and
`s = rk(R_R) ≤ rk(M)`, then some `p ∈ M` has zero annihilator: `r ↦ p r` is
injective, so `pR ≅ R_R`. Embed `Q_Q` in `M_Q` and clear the denominator of the
image `m c⁻¹` of `1`. -/
theorem exists_injective_toSpanSingleton [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Module.Finite Rᵐᵒᵖ M] (h : goldieRank R R ≤ goldieRank R M) :
    ∃ p : M, Function.Injective (LinearMap.toSpanSingleton Rᵐᵒᵖ M p) := by
  have : Module.Finite (OppositeQuotientRing R) (FractionModule R M) :=
    OreModule.finite (oppositeSubmonoid R⁰) M
  rw [goldieRank_self] at h
  obtain ⟨v, hv⟩ := exists_injective_smul_of_length_le h
  induction v using OreLocalization.ind with | _ m c =>
  refine ⟨m, ?_⟩
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro a ha
  rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at ha
  have h0 : ((a * c) /ₒ (1 : oppositeSubmonoid R⁰)) • (m /ₒ c) = 0 := by
    rw [OreModule.oreDiv_one_smul_eq, mul_smul, OreModule.smul_oreDiv_self,
      ← map_smul, ha, map_zero]
  have h1 : ((a * c) /ₒ (1 : oppositeSubmonoid R⁰) : OppositeQuotientRing R) = 0 :=
    hv (by
      dsimp only
      rw [h0]
      exact (zero_smul (OppositeQuotientRing R) (m /ₒ c : FractionModule R M)).symm)
  have h2 : a * c = 0 := numeratorRingHom_injective (h1.trans (map_zero _).symm)
  exact (Submodule.mem_bot _).mpr
    ((mem_oppositeSubmonoid_nonZeroDivisors.mp c.2).2 a h2)

/-- **Splitting off `R_R`.** If `rk(R_R) ≤ rk(M)`, there is `p ∈ M`
with `rk(M) = rk(R_R) + rk(M/pR)`. -/
theorem exists_goldieRank_eq_add_quotient [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Module.Finite Rᵐᵒᵖ M] (h : goldieRank R R ≤ goldieRank R M) :
    ∃ p : M, goldieRank R M =
      goldieRank R R + goldieRank R (M ⧸ Submodule.span Rᵐᵒᵖ {p}) := by
  obtain ⟨p, hp⟩ := exists_injective_toSpanSingleton h
  refine ⟨p, ?_⟩
  have hexact : Function.Exact (LinearMap.toSpanSingleton Rᵐᵒᵖ M p)
      (Submodule.span Rᵐᵒᵖ {p}).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
    exact LinearMap.span_singleton_eq_range Rᵐᵒᵖ M p
  rw [goldieRank_eq_add_of_exact hp (Submodule.mkQ_surjective _) hexact, goldieRank_op_self,
    ← goldieRank_self]

/-- **Successive choice.** Let `e_0, …, e_{n-1}` be nonzero elements of the
simple right Noetherian ring `R` and `rk(M) = l < n`. There are `m_j ∈ M`, with
`m_j = 0` for `j ≥ l`, such that the fractions of the `m_j e_j` span `M_Q` over
`Q`. Each choice raises the length of the span by at least one until it
reaches `l`, by the simplicity argument
(`eq_top_of_forall_toFractionModule_smul_mem`). -/
theorem exists_span_fraction_eq_top [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    [Module.Finite Rᵐᵒᵖ M] {n l : ℕ} (e : Fin n → R)
    (he : ∀ j, e j ≠ 0) (hln : l < n) (hM : goldieRank R M = l) :
    ∃ m : Fin n → M, (∀ j : Fin n, l ≤ (j : ℕ) → m j = 0) ∧
      Submodule.span (OppositeQuotientRing R)
        (Set.range fun j => toFractionModule R M (op (e j) • m j)) = ⊤ := by
  classical
  have : Module.Finite (OppositeQuotientRing R) (FractionModule R M) :=
    OreModule.finite (oppositeSubmonoid R⁰) M
  let U : (Fin n → M) → Submodule (OppositeQuotientRing R) (FractionModule R M) := fun m =>
    Submodule.span (OppositeQuotientRing R)
      (Set.range fun j => toFractionModule R M (op (e j) • m j))
  have hlenM : Module.length (OppositeQuotientRing R) (FractionModule R M) = l := hM
  have key : ∀ k ≤ l, ∃ m : Fin n → M, (∀ j : Fin n, k ≤ (j : ℕ) → m j = 0) ∧
      (k : ℕ∞) ≤ Module.length (OppositeQuotientRing R) (U m) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨0, fun _ _ => rfl, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨m, hm0, hmk⟩ := ih (by omega)
      by_cases hlen : ((k + 1 : ℕ) : ℕ∞) ≤ Module.length (OppositeQuotientRing R) (U m)
      · exact ⟨m, fun j hj => hm0 j (by omega), hlen⟩
      have hU : U m ≠ ⊤ := by
        intro htop
        apply hlen
        rw [htop, Module.length_top, hlenM]
        exact_mod_cast hk
      let i : Fin n := ⟨k, by omega⟩
      obtain ⟨m', hm'⟩ : ∃ m' : M, toFractionModule R M (op (e i) • m') ∉ U m := by
        by_contra! h
        exact hU (eq_top_of_forall_toFractionModule_smul_mem (he i) _ h)
      refine ⟨Function.update m i m', fun j hj => ?_, ?_⟩
      · have hji : j ≠ i := fun h => by rw [h] at hj; simp [i] at hj
        rw [Function.update_of_ne hji]
        exact hm0 j (by omega)
      have hlt : U m < U (Function.update m i m') := by
        refine lt_of_le_of_ne (Submodule.span_le.mpr ?_) ?_
        · rintro _ ⟨j, rfl⟩
          by_cases hj : j = i
          · rw [hj]
            dsimp only
            rw [hm0 i le_rfl, smul_zero, map_zero]
            exact zero_mem _
          · exact Submodule.subset_span ⟨j, by simp [Function.update_of_ne hj]⟩
        · intro heq
          apply hm'
          rw [heq]
          exact Submodule.subset_span ⟨i, by simp⟩
      have h1 := Submodule.height_strictMono hlt
      rw [← Module.length_submodule, ← Module.length_submodule] at h1
      push_cast
      exact Order.add_one_le_of_lt (lt_of_le_of_lt hmk h1)
  obtain ⟨m, hm0, hml⟩ := key l le_rfl
  refine ⟨m, hm0, ?_⟩
  by_contra hne
  have := Submodule.length_lt hne
  rw [hlenM] at this
  exact (lt_of_le_of_lt hml this).false

end AlgebraicAnalysis.Goldie
