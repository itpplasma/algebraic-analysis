module
public import AlgebraicAnalysis.Filtration.SymbolNoetherian

@[expose] public section

/-!
# Surjective symbol presentations

A `RingFiltration.SymbolPresentation φ 𝒜` is a commutative graded algebra
`G = ⨁ 𝒜 n` together with `R`-linear maps `σₙ : 𝒜ₙ → Fₙ/Fₙ₋₁` which are
surjective and multiplicative: `σ_{i+j}(g h) = σᵢ(g) σⱼ(h)` in the associated
graded module of `A`. Unlike `GradedSymbol`, the `σₙ` need not be injective.
So `gr A` is a quotient of the commutative graded algebra `G`, not isomorphic
to it. This is the situation of a graded quotient of a symmetric algebra,
such as `S(𝔤) ↠ gr U(𝔤)`, where the enveloping algebra has no PBW theorem
available.

`GradedSymbol.toPresentation` shows that an isomorphism-type symbol is a
presentation, so the results here contain those of `SymbolNoetherian`.

## Main results

The argument is that of `SymbolNoetherian`, with one change. For an additive
subgroup `T ≤ A`, `grPiece T n` is the set of homogeneous `g ∈ 𝒜ₙ` with
`σₙ(g) = [u]` for some `u ∈ T ∩ Fₙ`. Surjectivity of `σₙ` makes every class
of `Fₙ/Fₙ₋₁` realised by some `g`, which is all that the equality step needs.
Commutativity of `G` and multiplicativity of `σ` give that `gr T` is an ideal
for one-sided ideals `T`. Hence `I ↦ gr I` is strictly monotone.

* `SymbolPresentation.isNoetherian_right`, `isNoetherianRing`: if `G` is
  Noetherian then `A` is right and left Noetherian [McConnell–Robson 1.6.9].
* `SymbolPresentation.devLE_right`, `devLE_left`: if moreover `ringKrullDim G ≤ m`,
  the ideal lattices of `A` have deviation at most `m` [MR 6.5.6, 6.4.8].
* `SymbolPresentation.devLEOmega_right`, `devLEOmega_left`: finite Krull
  dimension of `G` gives deviation at most omega.
-/

namespace AlgebraicAnalysis

open DirectSum MulOpposite

namespace RingFiltration

/-- A surjective symbol presentation of `φ` by the commutative graded algebra
`G = ⨁ 𝒜 n`: surjective `R`-linear maps `σₙ : 𝒜ₙ → Fₙ/Fₙ₋₁` which multiply. -/
structure SymbolPresentation {R A G : Type*} [CommRing R] [Ring A] [Algebra R A]
    [CommRing G] [Algebra R G] (φ : RingFiltration R A) (𝒜 : ℕ → Submodule R G) where
  /-- The degree-`n` presentation map `𝒜ₙ → Fₙ/Fₙ₋₁`. -/
  sym : ∀ n, 𝒜 n →ₗ[R] φ.GradedQuotient n
  /-- Every class of `Fₙ/Fₙ₋₁` is the image of a homogeneous element of degree `n`. -/
  sym_surjective : ∀ n, Function.Surjective (sym n)
  /-- Multiplicativity: if `x = g h` in `G`, then `σ_{i+j}(x) = σᵢ(g) σⱼ(h)`. -/
  sym_mul : ∀ (i j : ℕ) (g : 𝒜 i) (h : 𝒜 j) (x : 𝒜 (i + j)),
    (x : G) = (g : G) * (h : G) → sym (i + j) x = φ.gradedMul i j (sym i g) (sym j h)

namespace SymbolPresentation

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing G] [Algebra R G]
variable {φ : RingFiltration R A} {𝒜 : ℕ → Submodule R G} (P : SymbolPresentation φ 𝒜)

/-- The degree-`n` symbols of `T ∩ Fₙ`: homogeneous `g ∈ 𝒜ₙ` whose presentation
class is the class of some `u ∈ T ∩ Fₙ`. -/
def grPiece (T : AddSubgroup A) (n : ℕ) : AddSubgroup G where
  carrier := {g | ∃ hg : g ∈ 𝒜 n, ∃ u ∈ T, ∃ hu : u ∈ φ.F n,
    P.sym n ⟨g, hg⟩ = Submodule.Quotient.mk ⟨u, hu⟩}
  add_mem' := by
    rintro a b ⟨ha, u, hu, hu', he⟩ ⟨hb, v, hv, hv', hf⟩
    refine ⟨Submodule.add_mem _ ha hb, u + v, T.add_mem hu hv, Submodule.add_mem _ hu' hv', ?_⟩
    rw [show (⟨a + b, Submodule.add_mem _ ha hb⟩ : 𝒜 n) = ⟨a, ha⟩ + ⟨b, hb⟩ from rfl, map_add,
      he, hf, ← Submodule.Quotient.mk_add]
    rfl
  zero_mem' := ⟨Submodule.zero_mem _, 0, T.zero_mem, Submodule.zero_mem _, by
    rw [show (⟨0, Submodule.zero_mem _⟩ : 𝒜 n) = 0 from rfl, map_zero]
    exact (Submodule.Quotient.mk_zero _).symm⟩
  neg_mem' := by
    rintro a ⟨ha, u, hu, hu', he⟩
    refine ⟨Submodule.neg_mem _ ha, -u, T.neg_mem hu, Submodule.neg_mem _ hu', ?_⟩
    rw [show (⟨-a, Submodule.neg_mem _ ha⟩ : 𝒜 n) = -⟨a, ha⟩ from rfl, map_neg, he,
      ← Submodule.Quotient.mk_neg]
    rfl

/-- Membership in the degree-`n` symbol piece, unfolded. -/
theorem mem_grPiece {T : AddSubgroup A} {n : ℕ} {g : G} :
    g ∈ P.grPiece T n ↔ ∃ hg : g ∈ 𝒜 n, ∃ u ∈ T, ∃ hu : u ∈ φ.F n,
      P.sym n ⟨g, hg⟩ = Submodule.Quotient.mk ⟨u, hu⟩ := Iff.rfl

variable [GradedAlgebra 𝒜]

/-- The symbol span `gr T ⊆ G`: elements all of whose homogeneous components
lie in the degree-wise symbol pieces of `T`. -/
def grSpan (T : AddSubgroup A) : AddSubgroup G where
  carrier := {g | ∀ n, (decompose 𝒜 g n : G) ∈ P.grPiece T n}
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
    g ∈ P.grSpan T ↔ ∀ n, (decompose 𝒜 g n : G) ∈ P.grPiece T n := Iff.rfl

theorem grSpan_mono {T T' : AddSubgroup A} (h : T ≤ T') : P.grSpan T ≤ P.grSpan T' := by
  intro g hg n
  obtain ⟨hg', u, hu, hu', he⟩ := hg n
  exact ⟨hg', u, h hu, hu', he⟩

/-- A homogeneous element of degree `n` lying in the degree-`n` piece lies in `gr T`. -/
theorem mem_grSpan_of_mem {T : AddSubgroup A} {n : ℕ} {g : G} (hg : g ∈ 𝒜 n)
    (hgP : g ∈ P.grPiece T n) : g ∈ P.grSpan T := by
  classical
  intro m
  by_cases hmn : m = n
  · subst hmn
    rw [decompose_of_mem_same 𝒜 hg]
    exact hgP
  · rw [decompose_of_mem_ne 𝒜 hg (Ne.symm hmn)]
    exact AddSubgroup.zero_mem _

/-- A homogeneous element of `gr T` of degree `n` lies in the degree-`n` piece. -/
theorem mem_grPiece_of_mem_grSpan {T : AddSubgroup A} {n : ℕ} {g : G}
    (hg : g ∈ P.grSpan T) (hgn : g ∈ 𝒜 n) : g ∈ P.grPiece T n := by
  have := hg n
  rwa [decompose_of_mem_same 𝒜 hgn] at this

/-- **Equal symbols force equality.** If `T ≤ T'` and every symbol of `T'` is a
symbol of `T`, then `T = T'`. Surjectivity of the presentation realises each
class of `Fₙ/Fₙ₋₁` by a homogeneous element; exhaustiveness and `F (-1) = 0`
finish the induction. -/
theorem eq_of_le_of_grSpan_le {T T' : AddSubgroup A} (hle : T ≤ T')
    (hgr : P.grSpan T' ≤ P.grSpan T) : T = T' := by
  have key : ∀ (n : ℕ) (u : A), u ∈ T' → u ∈ φ.F n →
      ∃ v ∈ T, v ∈ φ.F n ∧ u - v ∈ φ.below n := by
    intro n u hu hn
    obtain ⟨⟨g, hg'⟩, hg⟩ := P.sym_surjective n (Submodule.Quotient.mk ⟨u, hn⟩)
    have hmem : g ∈ P.grPiece T' n := ⟨hg', u, hu, hn, hg⟩
    obtain ⟨_, v, hv, hvn, hgv⟩ :=
      P.mem_grPiece_of_mem_grSpan (hgr (P.mem_grSpan_of_mem hg' hmem)) hg'
    refine ⟨v, hv, hvn, ?_⟩
    have := (Submodule.Quotient.eq (φ.belowInF n)).mp (hg.symm.trans hgv)
    exact φ.mem_belowInF.mp this
  refine le_antisymm hle fun u hu => ?_
  obtain ⟨n, hn⟩ := φ.exists_mem_of_directed u
  induction n generalizing u with
  | zero =>
    obtain ⟨v, hv, _, hd⟩ := key 0 u hu hn
    rw [below_zero, Submodule.mem_bot, sub_eq_zero] at hd
    rw [hd]
    exact hv
  | succ n ih =>
    obtain ⟨v, hv, _, hd⟩ := key (n + 1) u hu hn
    rw [below_succ] at hd
    have := ih (u - v) (T'.sub_mem hu (hle hv)) hd
    simpa using T.add_mem this hv

/-- `T ↦ gr T` is strictly monotone on additive subgroups. -/
theorem strictMono_grSpan : StrictMono P.grSpan := by
  intro T T' hlt
  refine lt_of_le_of_ne (P.grSpan_mono hlt.le) fun he => hlt.ne ?_
  exact P.eq_of_le_of_grSpan_le hlt.le he.ge

/-- If homogeneous multiples of degree-wise symbols of `T` are again such
symbols, then `gr T` is closed under multiplication by `G`. -/
theorem mul_mem_grSpan {T : AddSubgroup A}
    (hT : ∀ i m (r g : G), r ∈ 𝒜 i → g ∈ P.grPiece T m → r * g ∈ P.grPiece T (i + m))
    (r : G) {g : G} (hg : g ∈ P.grSpan T) : r * g ∈ P.grSpan T := by
  classical
  intro n
  rw [show r * g = ∑ i ∈ (decompose 𝒜 r).support, (decompose 𝒜 r i : G) * g by
    rw [← Finset.sum_mul, sum_support_decompose]]
  rw [decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [coe_decompose_mul_of_left_mem 𝒜 n (decompose 𝒜 r i).2]
  split_ifs with hin
  · have := hT i (n - i) _ _ (decompose 𝒜 r i).2 (hg (n - i))
    rwa [Nat.add_sub_of_le hin] at this
  · exact AddSubgroup.zero_mem _

/-- The degree-wise pieces of a right ideal absorb homogeneous elements on the right.
The symbol of `r g` equals `σ(g) σ(r)` by commutativity of `G`. -/
theorem mul_mem_grPiece_right (I : Submodule Aᵐᵒᵖ A) {i m : ℕ} {r g : G} (hr : r ∈ 𝒜 i)
    (hg : g ∈ P.grPiece I.toAddSubgroup m) : r * g ∈ P.grPiece I.toAddSubgroup (m + i) := by
  obtain ⟨hg', u, hu, hu', he⟩ := hg
  obtain ⟨⟨v, hv⟩, hvr⟩ := Submodule.Quotient.mk_surjective (φ.belowInF i) (P.sym i ⟨r, hr⟩)
  have hrg : r * g ∈ 𝒜 (m + i) := by
    rw [mul_comm]
    exact SetLike.mul_mem_graded hg' hr
  refine ⟨hrg, u * v, ?_, φ.mul_mem_add hu' hv, ?_⟩
  · have := I.smul_mem (op v) hu
    rwa [op_smul_eq_mul] at this
  · rw [P.sym_mul m i ⟨g, hg'⟩ ⟨r, hr⟩ ⟨r * g, hrg⟩ (mul_comm r g), he, ← hvr,
      RingFiltration.gradedMul_mk]

/-- The degree-wise pieces of a left ideal absorb homogeneous elements on the left. -/
theorem mul_mem_grPiece_left (I : Submodule A A) {i m : ℕ} {r g : G} (hr : r ∈ 𝒜 i)
    (hg : g ∈ P.grPiece I.toAddSubgroup m) : r * g ∈ P.grPiece I.toAddSubgroup (i + m) := by
  obtain ⟨hg', u, hu, hu', he⟩ := hg
  obtain ⟨⟨v, hv⟩, hvr⟩ := Submodule.Quotient.mk_surjective (φ.belowInF i) (P.sym i ⟨r, hr⟩)
  have hrg : r * g ∈ 𝒜 (i + m) := SetLike.mul_mem_graded hr hg'
  refine ⟨hrg, v * u, ?_, φ.mul_mem_add hv hu', ?_⟩
  · have := I.smul_mem v hu
    rwa [smul_eq_mul] at this
  · rw [P.sym_mul i m ⟨r, hr⟩ ⟨g, hg'⟩ ⟨r * g, hrg⟩ rfl, ← hvr, he,
      RingFiltration.gradedMul_mk]

/-- The symbol ideal `gr I ⊆ G` of a right ideal `I` of `A`. -/
def grIdealRight (I : Submodule Aᵐᵒᵖ A) : Ideal G where
  carrier := P.grSpan I.toAddSubgroup
  add_mem' := AddSubgroup.add_mem _
  zero_mem' := AddSubgroup.zero_mem _
  smul_mem' r _ hg :=
    P.mul_mem_grSpan
      (fun _ _ _ _ hr hg => by
        rw [add_comm]
        exact P.mul_mem_grPiece_right I hr hg) r hg

/-- The symbol ideal `gr I ⊆ G` of a left ideal `I` of `A`. -/
def grIdealLeft (I : Submodule A A) : Ideal G where
  carrier := P.grSpan I.toAddSubgroup
  add_mem' := AddSubgroup.add_mem _
  zero_mem' := AddSubgroup.zero_mem _
  smul_mem' r _ hg :=
    P.mul_mem_grSpan (fun _ _ _ _ hr hg => P.mul_mem_grPiece_left I hr hg) r hg

theorem mem_grIdealRight {I : Submodule Aᵐᵒᵖ A} {g : G} :
    g ∈ P.grIdealRight I ↔ g ∈ P.grSpan I.toAddSubgroup := Iff.rfl

theorem mem_grIdealLeft {I : Submodule A A} {g : G} :
    g ∈ P.grIdealLeft I ↔ g ∈ P.grSpan I.toAddSubgroup := Iff.rfl

/-- `I ↦ gr I` is strictly monotone on right ideals. -/
theorem strictMono_grIdealRight : StrictMono P.grIdealRight :=
  fun _ _ hIJ => P.strictMono_grSpan (Submodule.toAddSubgroup_strictMono hIJ)

/-- `I ↦ gr I` is strictly monotone on left ideals. -/
theorem strictMono_grIdealLeft : StrictMono P.grIdealLeft :=
  fun _ _ hIJ => P.strictMono_grSpan (Submodule.toAddSubgroup_strictMono hIJ)

/-! ## Noetherian and deviation consequences -/

include P in
/-- **[MR 1.6.9], right side.** If `G` is commutative Noetherian and `gr A` is a
quotient of `G` by the presentation, then `A` is right Noetherian. -/
theorem isNoetherian_right [IsNoetherianRing G] : IsNoetherian Aᵐᵒᵖ A := by
  rw [isNoetherian_iff]
  have : WellFoundedGT (Ideal G) := isNoetherian_iff.mp inferInstance
  exact P.strictMono_grIdealRight.wellFoundedGT

include P in
/-- **[MR 1.6.9], left side.** -/
theorem isNoetherianRing [IsNoetherianRing G] : IsNoetherianRing A := by
  rw [IsNoetherianRing, isNoetherian_iff]
  have : WellFoundedGT (Ideal G) := isNoetherian_iff.mp inferInstance
  exact P.strictMono_grIdealLeft.wellFoundedGT

include P in
/-- **[MR 6.5.6 with 6.4.8], right side.** If `G` is commutative Noetherian of
Krull dimension at most `m`, the right ideals of `A` have deviation at most `m`. -/
theorem devLE_right [IsNoetherianRing G] (m : ℕ) (hm : ringKrullDim G ≤ m) :
    Module.DevLE Aᵐᵒᵖ m A :=
  Order.DevLE.of_strictMono (Module.devLE_of_ringKrullDim_le m hm) P.strictMono_grIdealRight

include P in
/-- **[MR 6.5.6 with 6.4.8], left side.** -/
theorem devLE_left [IsNoetherianRing G] (m : ℕ) (hm : ringKrullDim G ≤ m) :
    Module.DevLE A m A :=
  Order.DevLE.of_strictMono (Module.devLE_of_ringKrullDim_le m hm) P.strictMono_grIdealLeft

include P in
/-- Finite Krull dimension of `G` gives right deviation at most omega. -/
theorem devLEOmega_right [IsNoetherianRing G] (hm : ringKrullDim G ≠ ⊤) :
    Module.DevLEOmega Aᵐᵒᵖ A := by
  obtain ⟨m, hG⟩ := Module.devLE_exists_of_ringKrullDim_ne_top hm
  exact Module.DevLE.omega (R := Aᵐᵒᵖ) (Order.DevLE.of_strictMono hG P.strictMono_grIdealRight)

include P in
/-- Finite Krull dimension of `G` gives left deviation at most omega. -/
theorem devLEOmega_left [IsNoetherianRing G] (hm : ringKrullDim G ≠ ⊤) :
    Module.DevLEOmega A A := by
  obtain ⟨m, hG⟩ := Module.devLE_exists_of_ringKrullDim_ne_top hm
  exact Module.DevLE.omega (R := A) (Order.DevLE.of_strictMono hG P.strictMono_grIdealLeft)

end SymbolPresentation

end RingFiltration

namespace RingFiltration.GradedSymbol

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing G] [Algebra R G]
variable {φ : RingFiltration R A} {𝒜 : ℕ → Submodule R G}

/-- An isomorphism-type symbol is a surjective presentation: `σₙ` is the inverse
of the isomorphism `Fₙ/Fₙ₋₁ ≅ 𝒜ₙ` of `GradedSymbol.gradedQuotientEquiv`. -/
noncomputable def toPresentation (S : GradedSymbol φ 𝒜) : SymbolPresentation φ 𝒜 where
  sym n := (S.gradedQuotientEquiv n).symm.toLinearMap
  sym_surjective n := (S.gradedQuotientEquiv n).symm.surjective
  sym_mul i j g h x hx := by
    obtain ⟨a, ha⟩ := S.gr_surjective i g
    obtain ⟨b, hb⟩ := S.gr_surjective j h
    obtain ⟨c, hc⟩ := S.gr_surjective (i + j) x
    have hab : (a : A) * (b : A) ∈ φ.F (i + j) := φ.mul_mem_add a.2 b.2
    have hsymm : ∀ (n : ℕ) (y : φ.F n) (z : 𝒜 n), S.gr n y = z →
        (S.gradedQuotientEquiv n).symm z = Submodule.Quotient.mk y := by
      intro n y z hyz
      rw [LinearEquiv.symm_apply_eq, ← hyz, gradedQuotientEquiv_mk]
    have key : S.gr (i + j) (c - ⟨(a : A) * (b : A), hab⟩) = 0 := by
      rw [map_sub, sub_eq_zero]
      apply Subtype.ext
      rw [hc, S.gr_mul i j a b, ha, hb]
      exact hx
    show (S.gradedQuotientEquiv (i + j)).symm x = φ.gradedMul i j
      ((S.gradedQuotientEquiv i).symm g) ((S.gradedQuotientEquiv j).symm h)
    rw [hsymm i a g ha, hsymm j b h hb, hsymm (i + j) c x hc, RingFiltration.gradedMul_mk]
    exact (Submodule.Quotient.eq _).mpr (φ.mem_belowInF.mpr ((S.gr_eq_zero_iff _ _).mp key))

end RingFiltration.GradedSymbol

namespace RingFiltration.SymbolPresentation

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing G] [Algebra R G]
variable {φ : RingFiltration R A} {𝒜 : ℕ → Submodule R G}

/-- **An injective presentation is a symbol isomorphism.** If every `σₙ` is
injective, then `gr A ≅ G`: the symbol of `u ∈ Fₙ` is `σₙ⁻¹ [u]`. -/
noncomputable def toGradedSymbol [GradedAlgebra 𝒜] (P : SymbolPresentation φ 𝒜)
    (hinj : ∀ n, Function.Injective (P.sym n)) : GradedSymbol φ 𝒜 where
  gr n := (LinearEquiv.ofBijective (P.sym n) ⟨hinj n, P.sym_surjective n⟩).symm.toLinearMap ∘ₗ
    (φ.belowInF n).mkQ
  gr_surjective n := by
    intro g
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (P.sym n g)
    refine ⟨z, ?_⟩
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Submodule.mkQ_apply,
      hz]
    exact (LinearEquiv.ofBijective (P.sym n) ⟨hinj n, P.sym_surjective n⟩).symm_apply_apply g
  gr_eq_zero_iff n x := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      mem_belowInF]
  gr_mul i j x y := by
    set e := fun n => LinearEquiv.ofBijective (P.sym n) ⟨hinj n, P.sym_surjective n⟩
    have key : ∀ n (z : φ.F n), P.sym n ((e n).symm (Submodule.Quotient.mk z)) =
        Submodule.Quotient.mk z := fun n z => (e n).apply_symm_apply _
    let g : 𝒜 (i + j) := ⟨_, SetLike.GradedMul.mul_mem ((e i).symm (Submodule.Quotient.mk x)).2
      ((e j).symm (Submodule.Quotient.mk y)).2⟩
    have hg : (e (i + j)).symm (Submodule.Quotient.mk ⟨x * y, φ.mul_mem_add x.2 y.2⟩) = g := by
      rw [LinearEquiv.symm_apply_eq]
      change _ = P.sym (i + j) g
      rw [P.sym_mul i j _ _ g rfl, key, key, gradedMul_mk]
    exact congrArg Subtype.val hg

end RingFiltration.SymbolPresentation

end AlgebraicAnalysis
