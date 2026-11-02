module
public import AlgebraicAnalysis.Filtration.GradedSymbol
public import AlgebraicAnalysis.Module.DeviationKrullDim
public import AlgebraicAnalysis.Module.DeviationOmega
public import Mathlib.Algebra.Algebra.Opposite

@[expose] public section

/-!
# Filtered rings with commutative Noetherian associated graded ring

Let `φ` be an ascending, exhaustive filtration of the `R`-algebra `A` with
`1 ∈ F 0` and `F i F j ⊆ F (i+j)`, and let `S : φ.GradedSymbol 𝒜` identify
`gr A` with a commutative graded algebra `G = ⨁ 𝒜 n`. This file proves:

* `RingFiltration.GradedSymbol.isNoetherian_right` and `isNoetherianRing`:
  if `G` is Noetherian then `A` is right and left Noetherian
  [McConnell–Robson, *Noncommutative Noetherian Rings*, 1.6.9];
* `RingFiltration.GradedSymbol.devLE_right` and `devLE_left`: if moreover
  `ringKrullDim G ≤ m`, then the right- and left-ideal lattices of `A` have
  deviation at most `m` [MR 6.5.6 with 6.4.8], hence deviation at most omega.

## Proof

For an additive subgroup `T ≤ A`, `grSpan T ≤ G` consists of the elements
whose degree-`n` component is the degree-`n` symbol of an element of
`T ∩ F n`, for every `n`. If `T ≤ T'` and `grSpan T' ≤ grSpan T` then
`T = T'`: an element `u ∈ T' ∩ F n` has the same symbol as some `v ∈ T ∩ F n`,
so `u - v ∈ T' ∩ F (n-1)` and induction on `n` applies; exhaustiveness
finishes (`eq_of_le_of_grSpan_le`). For a one-sided ideal `T`, commutativity
of `G` makes `grSpan T` an ideal of `G`. Hence `I ↦ gr I` is a strictly
monotone map from right (or left) ideals of `A` to ideals of `G`. Strictly
monotone maps pull back the ascending chain condition and deviation bounds
(`Order.DevLE.of_strictMono`), and `Module.devLE_of_ringKrullDim_le` bounds
the deviation of `G` by its Krull dimension. Both sides use the same symbol
data; no opposite filtration has to be constructed because the definition of
`grSpan` is side-free.
-/

namespace AlgebraicAnalysis

namespace RingFiltration

namespace GradedSymbol

open DirectSum MulOpposite

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing G] [Algebra R G]
variable {φ : RingFiltration R A} {𝒜 : ℕ → Submodule R G} (S : GradedSymbol φ 𝒜)

/-! ## The symbol span of an additive subgroup -/

/-- The degree-`n` symbols of the elements of `T ∩ F n`. -/
def grPiece (T : AddSubgroup A) (n : ℕ) : AddSubgroup G where
  carrier := {g | ∃ u ∈ T, u ∈ φ.F n ∧ S.grAt n u = g}
  add_mem' := by
    rintro _ _ ⟨u, hu, hu', rfl⟩ ⟨v, hv, hv', rfl⟩
    refine ⟨u + v, T.add_mem hu hv, Submodule.add_mem _ hu' hv', ?_⟩
    rw [← sub_neg_eq_add, S.grAt_sub hu' (Submodule.neg_mem _ hv'),
      ← zero_sub v, S.grAt_sub (Submodule.zero_mem _) hv',
      show S.grAt n 0 = 0 from (S.grAt_eq_zero_iff (Submodule.zero_mem _)).mpr
        (Submodule.zero_mem _)]
    abel
  zero_mem' := ⟨0, T.zero_mem, Submodule.zero_mem _,
    (S.grAt_eq_zero_iff (Submodule.zero_mem _)).mpr (Submodule.zero_mem _)⟩
  neg_mem' := by
    rintro _ ⟨u, hu, hu', rfl⟩
    refine ⟨-u, T.neg_mem hu, Submodule.neg_mem _ hu', ?_⟩
    rw [← zero_sub, S.grAt_sub (Submodule.zero_mem _) hu',
      show S.grAt n 0 = 0 from (S.grAt_eq_zero_iff (Submodule.zero_mem _)).mpr
        (Submodule.zero_mem _), zero_sub]

theorem mem_grPiece {T : AddSubgroup A} {n : ℕ} {g : G} :
    g ∈ S.grPiece T n ↔ ∃ u ∈ T, u ∈ φ.F n ∧ S.grAt n u = g := Iff.rfl

variable [GradedAlgebra 𝒜]

/-- The symbol span `gr T`: elements of `G` all of whose homogeneous
components are symbols of elements of `T` in the corresponding degree. -/
def grSpan (T : AddSubgroup A) : AddSubgroup G where
  carrier := {g | ∀ n, (decompose 𝒜 g n : G) ∈ S.grPiece T n}
  add_mem' := by
    intro a b ha hb n
    rw [decompose_add, add_apply, Submodule.coe_add]
    exact AddSubgroup.add_mem _ (ha n) (hb n)
  zero_mem' := by
    intro n
    rw [decompose_zero, zero_apply, Submodule.coe_zero]
    exact AddSubgroup.zero_mem _
  neg_mem' := by
    intro a ha n
    rw [decompose_neg]
    erw [DFinsupp.neg_apply]
    rw [Submodule.coe_neg]
    exact AddSubgroup.neg_mem _ (ha n)

theorem mem_grSpan {T : AddSubgroup A} {g : G} :
    g ∈ S.grSpan T ↔ ∀ n, (decompose 𝒜 g n : G) ∈ S.grPiece T n := Iff.rfl

theorem grSpan_mono {T T' : AddSubgroup A} (h : T ≤ T') : S.grSpan T ≤ S.grSpan T' := by
  intro g hg n
  obtain ⟨u, hu, hu', he⟩ := hg n
  exact ⟨u, h hu, hu', he⟩

/-- The degree-`n` symbol of an element of `T ∩ F n` lies in `gr T`. -/
theorem grAt_mem_grSpan {T : AddSubgroup A} {n : ℕ} {u : A} (hu : u ∈ T)
    (hn : u ∈ φ.F n) : S.grAt n u ∈ S.grSpan T := by
  classical
  intro m
  by_cases hmn : m = n
  · subst hmn
    rw [decompose_of_mem_same 𝒜 (S.grAt_mem m u)]
    exact ⟨u, hu, hn, rfl⟩
  · rw [decompose_of_mem_ne 𝒜 (S.grAt_mem n u) (Ne.symm hmn)]
    exact AddSubgroup.zero_mem _

/-- A homogeneous element of degree `n` in `gr T` is the degree-`n` symbol of
an element of `T ∩ F n`. -/
theorem exists_of_mem_grSpan {T : AddSubgroup A} {n : ℕ} {g : G} (hg : g ∈ S.grSpan T)
    (hgn : g ∈ 𝒜 n) : ∃ u ∈ T, u ∈ φ.F n ∧ S.grAt n u = g := by
  have := hg n
  rwa [decompose_of_mem_same 𝒜 hgn] at this

/-- **Equal symbols force equality.** If `T ≤ T'` and every symbol of `T'`
is a symbol of `T`, then `T = T'`. This is where exhaustiveness and
`F (-1) = 0` of the filtration are used. -/
theorem eq_of_le_of_grSpan_le {T T' : AddSubgroup A} (hle : T ≤ T')
    (hgr : S.grSpan T' ≤ S.grSpan T) : T = T' := by
  refine le_antisymm hle fun u hu => ?_
  obtain ⟨n, hn⟩ := φ.exists_mem_of_directed u
  induction n generalizing u with
  | zero =>
    obtain ⟨v, hv, hv0, he⟩ :=
      S.exists_of_mem_grSpan (hgr (S.grAt_mem_grSpan hu hn)) (S.grAt_mem 0 u)
    have hd := (S.grAt_eq_grAt_iff hv0 hn).mp he
    rw [below_zero, Submodule.mem_bot, sub_eq_zero] at hd
    exact hd ▸ hv
  | succ n ih =>
    obtain ⟨v, hv, hvn, he⟩ :=
      S.exists_of_mem_grSpan (hgr (S.grAt_mem_grSpan hu hn)) (S.grAt_mem (n + 1) u)
    have hd := (S.grAt_eq_grAt_iff hn hvn).mp he.symm
    rw [below_succ] at hd
    have := ih (u - v) (T'.sub_mem hu (hle hv)) hd
    simpa using T.add_mem this hv

/-- `T ↦ gr T` is strictly monotone on additive subgroups. -/
theorem strictMono_grSpan : StrictMono S.grSpan := by
  intro T T' hlt
  refine lt_of_le_of_ne (S.grSpan_mono hlt.le) fun he => hlt.ne ?_
  exact S.eq_of_le_of_grSpan_le hlt.le he.ge

/-! ## Symbol ideals of one-sided ideals -/

/-- If homogeneous multiples of symbols of `T` are again symbols of `T`, then
`gr T` is closed under multiplication by `G`. -/
theorem mul_mem_grSpan {T : AddSubgroup A}
    (hT : ∀ i m (r g : G), r ∈ 𝒜 i → g ∈ S.grPiece T m → r * g ∈ S.grPiece T (m + i))
    (r : G) {g : G} (hg : g ∈ S.grSpan T) : r * g ∈ S.grSpan T := by
  classical
  intro n
  rw [show r * g = ∑ i ∈ (decompose 𝒜 r).support, (decompose 𝒜 r i : G) * g by
    rw [← Finset.sum_mul, sum_support_decompose]]
  rw [decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [coe_decompose_mul_of_left_mem 𝒜 n (decompose 𝒜 r i).2]
  split_ifs with hin
  · have := hT i (n - i) _ _ (decompose 𝒜 r i).2 (hg (n - i))
    rwa [Nat.sub_add_cancel hin] at this
  · exact AddSubgroup.zero_mem _

omit [GradedAlgebra 𝒜] in
/-- The symbol pieces of a right ideal absorb homogeneous elements. -/
theorem mul_mem_grPiece_right (I : Submodule Aᵐᵒᵖ A) {i m : ℕ} {r g : G}
    (hr : r ∈ 𝒜 i) (hg : g ∈ S.grPiece I.toAddSubgroup m) :
    r * g ∈ S.grPiece I.toAddSubgroup (m + i) := by
  obtain ⟨u, hu, hu', rfl⟩ := hg
  obtain ⟨v, hv, rfl⟩ := S.exists_grAt_eq hr
  refine ⟨u * v, ?_, φ.mul_mem_add hu' hv, ?_⟩
  · have := I.smul_mem (op v) hu
    rwa [op_smul_eq_mul] at this
  · rw [S.grAt_mul hu' hv, mul_comm]

omit [GradedAlgebra 𝒜] in
/-- The symbol pieces of a left ideal absorb homogeneous elements. -/
theorem mul_mem_grPiece_left (I : Submodule A A) {i m : ℕ} {r g : G}
    (hr : r ∈ 𝒜 i) (hg : g ∈ S.grPiece I.toAddSubgroup m) :
    r * g ∈ S.grPiece I.toAddSubgroup (m + i) := by
  obtain ⟨u, hu, hu', rfl⟩ := hg
  obtain ⟨v, hv, rfl⟩ := S.exists_grAt_eq hr
  refine ⟨v * u, ?_, add_comm i m ▸ φ.mul_mem_add hv hu', ?_⟩
  · have := I.smul_mem v hu
    rwa [smul_eq_mul] at this
  · rw [S.grAt_mul' (add_comm i m) hv hu']

/-- The symbol ideal `gr I ⊆ G` of a right ideal `I` of `A`. -/
def grIdealRight (I : Submodule Aᵐᵒᵖ A) : Ideal G where
  carrier := S.grSpan I.toAddSubgroup
  add_mem' := AddSubgroup.add_mem _
  zero_mem' := AddSubgroup.zero_mem _
  smul_mem' r _ hg :=
    S.mul_mem_grSpan (fun _ _ _ _ hr hg => S.mul_mem_grPiece_right I hr hg) r hg

/-- The symbol ideal `gr I ⊆ G` of a left ideal `I` of `A`. -/
def grIdealLeft (I : Submodule A A) : Ideal G where
  carrier := S.grSpan I.toAddSubgroup
  add_mem' := AddSubgroup.add_mem _
  zero_mem' := AddSubgroup.zero_mem _
  smul_mem' r _ hg :=
    S.mul_mem_grSpan (fun _ _ _ _ hr hg => S.mul_mem_grPiece_left I hr hg) r hg

theorem mem_grIdealRight {I : Submodule Aᵐᵒᵖ A} {g : G} :
    g ∈ S.grIdealRight I ↔ g ∈ S.grSpan I.toAddSubgroup := Iff.rfl

theorem mem_grIdealLeft {I : Submodule A A} {g : G} :
    g ∈ S.grIdealLeft I ↔ g ∈ S.grSpan I.toAddSubgroup := Iff.rfl

/-- Right ideals with comparable members and equal symbol ideals coincide:
`I ↦ gr I` is strictly monotone. -/
theorem strictMono_grIdealRight : StrictMono S.grIdealRight :=
  fun _ _ hIJ => S.strictMono_grSpan (Submodule.toAddSubgroup_strictMono hIJ)

/-- Left ideals with comparable members and equal symbol ideals coincide:
`I ↦ gr I` is strictly monotone. -/
theorem strictMono_grIdealLeft : StrictMono S.grIdealLeft :=
  fun _ _ hIJ => S.strictMono_grSpan (Submodule.toAddSubgroup_strictMono hIJ)

/-! ## Noetherian and deviation consequences -/

include S in
/-- **[MR 1.6.9], right side.** If `gr A ≅ G` is a commutative Noetherian
ring, then `A` is right Noetherian. -/
theorem isNoetherian_right [IsNoetherianRing G] : IsNoetherian Aᵐᵒᵖ A := by
  rw [isNoetherian_iff]
  have : WellFoundedGT (Ideal G) := isNoetherian_iff.mp inferInstance
  exact S.strictMono_grIdealRight.wellFoundedGT

include S in
/-- **[MR 1.6.9], left side.** If `gr A ≅ G` is a commutative Noetherian
ring, then `A` is left Noetherian. -/
theorem isNoetherianRing [IsNoetherianRing G] : IsNoetherianRing A := by
  rw [IsNoetherianRing, isNoetherian_iff]
  have : WellFoundedGT (Ideal G) := isNoetherian_iff.mp inferInstance
  exact S.strictMono_grIdealLeft.wellFoundedGT

include S in
/-- **[MR 6.5.6 with 6.4.8], right side.** If `gr A ≅ G` is commutative
Noetherian of Krull dimension at most `m`, the right ideals of `A` form a
lattice of deviation at most `m`. -/
theorem devLE_right [IsNoetherianRing G] (m : ℕ) (hm : ringKrullDim G ≤ m) :
    Module.DevLE Aᵐᵒᵖ m A :=
  Order.DevLE.of_strictMono (Module.devLE_of_ringKrullDim_le m hm) S.strictMono_grIdealRight

include S in
/-- **[MR 6.5.6 with 6.4.8], left side.** If `gr A ≅ G` is commutative
Noetherian of Krull dimension at most `m`, the left ideals of `A` form a
lattice of deviation at most `m`. -/
theorem devLE_left [IsNoetherianRing G] (m : ℕ) (hm : ringKrullDim G ≤ m) :
    Module.DevLE A m A :=
  Order.DevLE.of_strictMono (Module.devLE_of_ringKrullDim_le m hm) S.strictMono_grIdealLeft

include S in
/-- Finite Krull dimension of `gr A` gives right deviation at most omega. -/
theorem devLEOmega_right [IsNoetherianRing G] (hm : ringKrullDim G ≠ ⊤) :
    Module.DevLEOmega Aᵐᵒᵖ A := by
  obtain ⟨m, hG⟩ := Module.devLE_exists_of_ringKrullDim_ne_top hm
  exact Module.DevLE.omega (R := Aᵐᵒᵖ)
    (Order.DevLE.of_strictMono hG S.strictMono_grIdealRight)

include S in
/-- Finite Krull dimension of `gr A` gives left deviation at most omega. -/
theorem devLEOmega_left [IsNoetherianRing G] (hm : ringKrullDim G ≠ ⊤) :
    Module.DevLEOmega A A := by
  obtain ⟨m, hG⟩ := Module.devLE_exists_of_ringKrullDim_ne_top hm
  exact Module.DevLE.omega (R := A)
    (Order.DevLE.of_strictMono hG S.strictMono_grIdealLeft)

end GradedSymbol

end RingFiltration

end AlgebraicAnalysis
