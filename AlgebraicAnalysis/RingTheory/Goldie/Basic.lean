module

public import AlgebraicAnalysis.Module.DenominatorTorsion

@[expose] public section

/-!
# Goldie theory for simple right Noetherian rings

Let `R` be a simple ring which is right Noetherian (`IsNoetherian Rᵐᵒᵖ R`); zero
divisors are allowed. This file proves the ring-theoretic half of Goldie's
theorem:

* the right singular ideal vanishes (`eq_zero_of_isEssential_rightAnn`);
* every nonzero right ideal contains a nonzero good element `b`, i.e. one with
  `bR ∩ r(b) = 0` (`exists_good_mem`);
* an element with zero right annihilator generates an essential right ideal
  and is regular (`isEssential_principal`, `mem_nonZeroDivisors_of_rightAnn`);
* every essential right ideal contains a regular element
  (`exists_mem_nonZeroDivisors_of_isEssential`);
* the regular elements satisfy the right Ore condition (`exists_right_ore`),
  so finitely many right ideals containing regular elements have a common
  regular element (`exists_mem_nonZeroDivisors_finset`), and `(Rᵐᵒᵖ)⁰` is an
  Ore set in Mathlib's convention (`nonempty_oreSet_op`);
* every right ideal `I` contains an element `a` such that `I / aR` is
  Goldie-torsion: each `y ∈ I` has a regular `s` with `y s ∈ aR`
  (`exists_mem_forall_exists_mul_mem`).

Right ideals are `Submodule Rᵐᵒᵖ R`; `x * y` is always read in the displayed
order. "Regular" means two-sided regular, `s ∈ R⁰`. An essential right ideal
`E` is one meeting every nonzero right ideal; in elements, every `y ≠ 0` has a
right multiple `y r ≠ 0` in `E`.

## Proof of the last statement

Let `C` be a right ideal maximal with `I ∩ C = 0` (it exists because `R` is
right Noetherian). Then `I + C` is essential: if `y ≠ 0` and `yR ∩ (I + C) = 0`,
then `I ∩ (C + yR) = 0` and `C + yR` strictly contains `C`. By Goldie,
`I + C` contains a regular `s = a + c` with `a ∈ I`, `c ∈ C`. For `y ∈ I` the
right ideal `{r | y r ∈ sR}` is essential, as the inverse image of the
essential right ideal `sR`, so it contains a regular `t`; write `y t = s r'`.
Then `c r' = y t - a r'` lies in `I ∩ C = 0`, so `y t = a r'`.

## References

The argument follows the classical proof (A. W. Goldie, *The structure of
prime rings under ascending chain conditions*, Proc. London Math. Soc. (3) 8
(1958) 589–608, and *Semi-prime rings with maximum condition*, ibid. 10 (1960)
201–220; J. C. McConnell and J. C. Robson, *Noncommutative Noetherian Rings*,
§2.3, in particular 2.3.6 and 2.3.10; K. R. Goodearl and R. B. Warfield, *An
Introduction to Noncommutative Noetherian Rings*, Ch. 5–6), specialized to
simple rings: simplicity replaces semiprimeness and the nilpotency of the
singular ideal, and the right Noetherian hypothesis replaces finite uniform
dimension and the ascending chain condition on right annihilators. Nothing
here is new.
-/

namespace AlgebraicAnalysis.Goldie

open MulOpposite nonZeroDivisors AlgebraicAnalysis.DenominatorTorsion

universe u
variable {R : Type u} [Ring R]

/-- The right annihilator `r(x) = {y | x y = 0}` as a right ideal. -/
def rightAnn (x : R) : Submodule Rᵐᵒᵖ R := LinearMap.ker (leftMulLinear x)

theorem mem_rightAnn {x y : R} : y ∈ rightAnn x ↔ x * y = 0 := Iff.rfl

theorem mem_principalRightIdeal {x y : R} :
    y ∈ principalRightIdeal x ↔ ∃ r, x * r = y := Iff.rfl

/-- An essential right ideal: every nonzero `y` has a nonzero right multiple
`y r` in `E`, i.e. `E` meets every nonzero right ideal nontrivially. -/
def IsEssential (E : Submodule Rᵐᵒᵖ R) : Prop :=
  ∀ y : R, y ≠ 0 → ∃ r : R, y * r ≠ 0 ∧ y * r ∈ E

theorem IsEssential.mono {E F : Submodule Rᵐᵒᵖ R} (hE : IsEssential E) (h : E ≤ F) :
    IsEssential F := fun y hy => by
  obtain ⟨r, hr, hrE⟩ := hE y hy
  exact ⟨r, hr, h hrE⟩

theorem IsEssential.inf {E F : Submodule Rᵐᵒᵖ R} (hE : IsEssential E) (hF : IsEssential F) :
    IsEssential (E ⊓ F) := fun y hy => by
  obtain ⟨r, hr, hrE⟩ := hE y hy
  obtain ⟨r', hr', hr'F⟩ := hF (y * r) hr
  refine ⟨r * r', by rwa [← mul_assoc], ?_, by rwa [← mul_assoc]⟩
  have := E.smul_mem (op r') hrE
  rwa [op_smul_eq_mul, mul_assoc] at this

/-- The inverse image `{y | a y ∈ E}` of an essential right ideal is essential. -/
theorem IsEssential.comap {E : Submodule Rᵐᵒᵖ R} (hE : IsEssential E) (a : R) :
    IsEssential (E.comap (leftMulLinear a)) := fun y hy => by
  by_cases hay : a * y = 0
  · refine ⟨1, by rwa [mul_one], ?_⟩
    change a * (y * 1) ∈ E
    rw [mul_one, hay]
    exact E.zero_mem
  · obtain ⟨r, hr, hrE⟩ := hE (a * y) hay
    refine ⟨r, fun h => hr (by rw [mul_assoc, h, mul_zero]), ?_⟩
    change a * (y * r) ∈ E
    rwa [← mul_assoc]

theorem not_isEssential_bot [Nontrivial R] : ¬ IsEssential (⊥ : Submodule Rᵐᵒᵖ R) := by
  intro h
  obtain ⟨r, hr, hr0⟩ := h 1 one_ne_zero
  exact hr ((Submodule.mem_bot _).mp hr0)

theorem IsEssential.exists_ne_zero_mem_inf {E K : Submodule Rᵐᵒᵖ R} (hE : IsEssential E)
    (hK : K ≠ ⊥) : ∃ y ∈ E ⊓ K, y ≠ 0 := by
  obtain ⟨z, hzK, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  obtain ⟨r, hr, hrE⟩ := hE z hz
  refine ⟨z * r, ⟨hrE, ?_⟩, hr⟩
  have := K.smul_mem (op r) hzK
  rwa [op_smul_eq_mul] at this

/-! ## The right singular ideal of a simple ring vanishes -/

/-- The right singular ideal `Z(R_R) = {y | r(y) essential}`. -/
def singularIdeal (R : Type u) [Ring R] : TwoSidedIdeal R :=
  TwoSidedIdeal.mk' {y : R | IsEssential (rightAnn y)}
    (fun y hy => ⟨1, by rwa [mul_one], by
      change (0 : R) * (y * 1) = 0
      rw [zero_mul]⟩)
    (fun {x y} hx hy => (IsEssential.inf hx hy).mono fun z hz => by
      change (x + y) * z = 0
      rw [add_mul, mem_rightAnn.mp hz.1, mem_rightAnn.mp hz.2, add_zero])
    (fun {x} hx => hx.mono fun z hz => by
      change -x * z = 0
      rw [neg_mul, mem_rightAnn.mp hz, neg_zero])
    (fun {x y} hy => hy.mono fun z hz => by
      change x * y * z = 0
      rw [mul_assoc, mem_rightAnn.mp hz, mul_zero])
    (fun {x y} hx => (hx.comap y).mono fun z hz => by
      change x * (y * z) = 0 at hz
      change x * y * z = 0
      rwa [mul_assoc])

/-- **The right singular ideal of a simple ring is zero.** -/
theorem eq_zero_of_isEssential_rightAnn [IsSimpleRing R] {y : R}
    (hy : IsEssential (rightAnn y)) : y = 0 := by
  by_contra hne
  have h1 : (1 : R) ∈ singularIdeal R :=
    IsSimpleRing.one_mem_of_ne_zero_mem _ hne
      ((TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mpr hy)
  have h1' : IsEssential (rightAnn (1 : R)) := (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mp h1
  obtain ⟨r, hr, hr0⟩ := h1' 1 one_ne_zero
  have : (1 : R) * (1 * r) = 0 := hr0
  exact hr (by simpa using this)

/-! ## Good elements -/

/-- `x` is *good* if `xR ∩ r(x) = 0`. -/
def IsGood (x : R) : Prop := ∀ z : R, x * (x * z) = 0 → x * z = 0

/-- A simple right Noetherian ring has no nonzero nil right ideal. -/
theorem exists_not_nilpotent_mem [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {K : Submodule Rᵐᵒᵖ R} (hK : K ≠ ⊥) : ∃ a ∈ K, ∀ n : ℕ, a ^ n ≠ 0 := by
  classical
  by_contra! hnil
  obtain ⟨_, ⟨a, haK, ha0, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := Rᵐᵒᵖ) (M := R)).mpr inferInstance
      {L | ∃ a ∈ K, a ≠ 0 ∧ rightAnn a = L}
      (by
        obtain ⟨a, haK, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
        exact ⟨_, a, haK, ha, rfl⟩)
  -- `a R a = 0`.
  have haxa : ∀ x : R, a * x * a = 0 := by
    intro x
    by_contra hne
    set y := x * a with hy
    have hay : a * y ≠ 0 := by rwa [hy, ← mul_assoc]
    have haxK : a * x ∈ K := by
      have := K.smul_mem (op x) haK
      rwa [op_smul_eq_mul] at this
    obtain ⟨m, hm⟩ := hnil (a * x) haxK
    have hex : ∃ n, a * y ^ (n + 1) = 0 := ⟨m, by
      rw [hy, ← mul_pow_mul, pow_succ, hm, zero_mul, zero_mul]⟩
    set t := Nat.find hex with ht
    have hta : a * y ^ (t + 1) = 0 := Nat.find_spec hex
    have hc0 : a * y ^ t ≠ 0 := by
      rcases Nat.eq_zero_or_eq_succ_pred t with h0 | hs
      · rw [h0, pow_zero, mul_one]; exact ha0
      · rw [hs]
        exact Nat.find_min hex (by omega)
    have hcK : a * y ^ t ∈ K := by
      have := K.smul_mem (op (y ^ t)) haK
      rwa [op_smul_eq_mul] at this
    have hle : rightAnn a ≤ rightAnn (a * y ^ t) := by
      intro z hz
      change a * y ^ t * z = 0
      rw [hy, ← mul_pow_mul, mul_assoc, mem_rightAnn.mp hz, mul_zero]
    have heq : rightAnn a = rightAnn (a * y ^ t) := by
      by_contra hne'
      exact hmax _ ⟨_, hcK, hc0, rfl⟩ (lt_of_le_of_ne hle hne')
    have hyann : y ∈ rightAnn (a * y ^ t) := by
      change a * y ^ t * y = 0
      rw [mul_assoc, ← pow_succ, hta]
    rw [← heq] at hyann
    exact hay hyann
  -- Simplicity: the two-sided ideal `{c | a R c = 0}` contains `a`.
  let J : TwoSidedIdeal R := TwoSidedIdeal.mk' {c | ∀ r : R, a * r * c = 0}
    (fun r => mul_zero _)
    (fun {x y} hx hy r => by rw [mul_add, hx r, hy r, add_zero])
    (fun {x} hx r => by rw [mul_neg, hx r, neg_zero])
    (fun {x y} hy r => by rw [← mul_assoc, mul_assoc a r x, hy])
    (fun {x y} hx r => by rw [← mul_assoc, hx r, zero_mul])
  have h1 : (1 : R) ∈ J := IsSimpleRing.one_mem_of_ne_zero_mem J ha0
    (by simpa [J, TwoSidedIdeal.mem_mk'] using haxa)
  have h1' : ∀ r : R, a * r * 1 = 0 := by simpa [J, TwoSidedIdeal.mem_mk'] using h1
  exact ha0 (by simpa using h1' 1)

/-- Every nonzero right ideal of a simple right Noetherian ring contains a
nonzero good element. -/
theorem exists_good_mem [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {K : Submodule Rᵐᵒᵖ R} (hK : K ≠ ⊥) : ∃ b ∈ K, b ≠ 0 ∧ IsGood b := by
  obtain ⟨a, haK, hnil⟩ := exists_not_nilpotent_mem hK
  have hmono : Monotone fun n : ℕ => rightAnn (a ^ n) := by
    refine monotone_nat_of_le_succ fun n z hz => ?_
    change a ^ (n + 1) * z = 0
    rw [pow_succ', mul_assoc, mem_rightAnn.mp hz, mul_zero]
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := Rᵐᵒᵖ) (M := R)).mpr
    inferInstance ⟨_, hmono⟩
  have h1 : rightAnn (a ^ (n + 1)) = rightAnn (a ^ (n + 1 + (n + 1))) := by
    have e1 := hn (n + 1) (by omega)
    have e2 := hn (n + 1 + (n + 1)) (by omega)
    exact e1.symm.trans e2
  refine ⟨a ^ (n + 1), ?_, hnil _, fun z hz => ?_⟩
  · have := K.smul_mem (op (a ^ n)) haK
    rwa [op_smul_eq_mul, ← pow_succ'] at this
  · have hz' : z ∈ rightAnn (a ^ (n + 1 + (n + 1))) := by
      change a ^ (n + 1 + (n + 1)) * z = 0
      rwa [pow_add, mul_assoc]
    rw [← h1] at hz'
    exact hz'

/-! ## Essential right ideals contain regular elements -/

/-- Every essential right ideal contains an element with zero right
annihilator. -/
theorem exists_mem_rightAnn_eq_bot [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {E : Submodule Rᵐᵒᵖ R} (hE : IsEssential E) :
    ∃ x ∈ E, ∀ z : R, x * z = 0 → z = 0 := by
  classical
  obtain ⟨L, ⟨x, hxE, hxg, hLx⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := Rᵐᵒᵖ) (M := R)).mpr inferInstance
      {L | ∃ x ∈ E, IsGood x ∧ L ⊓ rightAnn x = ⊥}
      ⟨⊥, 0, E.zero_mem, fun z _ => by rw [zero_mul], bot_inf_eq _⟩
  refine ⟨x, hxE, ?_⟩
  by_contra! hex
  have hann : rightAnn x ≠ ⊥ := by
    obtain ⟨z, hz, hz0⟩ := hex
    intro h
    have : z ∈ rightAnn x := hz
    rw [h] at this
    exact hz0 ((Submodule.mem_bot _).mp this)
  obtain ⟨y, hy, hy0⟩ := hE.exists_ne_zero_mem_inf hann
  have hEK : E ⊓ rightAnn x ≠ ⊥ := fun h => hy0 ((Submodule.mem_bot _).mp (h ▸ hy))
  obtain ⟨a, ⟨haE, hax⟩, ha0, hag⟩ := exists_good_mem hEK
  have hxa : x * a = 0 := hax
  -- `r(x + a) = r(x) ∩ r(a)`.
  have hann' : ∀ w : R, (x + a) * w = 0 → x * w = 0 ∧ a * w = 0 := by
    intro w hw
    have hxw : x * (x * w) = 0 := by
      have h2 : x * w = -(a * w) := eq_neg_of_add_eq_zero_left (by rwa [← add_mul])
      rw [h2, mul_neg, ← mul_assoc, hxa, zero_mul, neg_zero]
    have h1 := hxg w hxw
    refine ⟨h1, ?_⟩
    rwa [add_mul, h1, zero_add] at hw
  have hgood : IsGood (x + a) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hann' _ hz
    have hxz : x * z = 0 := hxg z (by
      rw [add_mul, mul_add, ← mul_assoc x a z, hxa, zero_mul, add_zero] at h1; exact h1)
    have haz : a * z = 0 := hag z (by
      rw [add_mul, mul_add, hxz, mul_zero, zero_add] at h2; exact h2)
    rw [add_mul, hxz, haz, add_zero]
  have hL' : L ⊔ principalRightIdeal a ∈ {L | ∃ x ∈ E, IsGood x ∧ L ⊓ rightAnn x = ⊥} := by
    refine ⟨x + a, E.add_mem hxE haE, hgood, ?_⟩
    rw [Submodule.eq_bot_iff]
    rintro m ⟨hm, hmann⟩
    obtain ⟨l, hl, _, ⟨s, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hm
    change l + a * s ∈ rightAnn (x + a) at hmann
    obtain ⟨h1, h2⟩ := hann' _ hmann
    have hxl : x * l = 0 := by
      rwa [mul_add, ← mul_assoc, hxa, zero_mul, add_zero] at h1
    have hl0 : l = 0 := by
      have : l ∈ L ⊓ rightAnn x := ⟨hl, hxl⟩
      rw [hLx] at this
      exact (Submodule.mem_bot _).mp this
    subst hl0
    rw [zero_add] at h2 ⊢
    exact hag s h2
  have hlt : L < L ⊔ principalRightIdeal a := by
    refine lt_of_le_of_ne le_sup_left fun h => ha0 ?_
    have haL : a ∈ L := h ▸ Submodule.mem_sup_right ⟨1, mul_one a⟩
    have : a ∈ L ⊓ rightAnn x := ⟨haL, hax⟩
    rw [hLx] at this
    exact (Submodule.mem_bot _).mp this
  exact hmax _ hL' hlt

/-- An element with zero right annihilator generates an essential right ideal
(right Noetherian rings have no infinite direct sums `K ⊕ xK ⊕ x²K ⊕ ⋯`). -/
theorem isEssential_principal [IsNoetherian Rᵐᵒᵖ R] {x : R}
    (hx : ∀ z : R, x * z = 0 → z = 0) : IsEssential (principalRightIdeal x) := by
  intro y hy
  by_contra! hdisj
  set K := principalRightIdeal y with hK
  set f := leftMulLinear x with hf
  have hKx : ∀ k ∈ K, k ∈ LinearMap.range f → k = 0 := by
    rintro _ ⟨r, rfl⟩ hk
    by_contra h
    exact hdisj r h hk
  let B : ℕ → Submodule Rᵐᵒᵖ R := fun n => Nat.rec ⊥ (fun _ b => K ⊔ b.map f) n
  have hB0 : B 0 = ⊥ := rfl
  have hBs : ∀ n, B (n + 1) = K ⊔ (B n).map f := fun _ => rfl
  have hmono : Monotone B := by
    refine monotone_nat_of_le_succ fun n => ?_
    induction n with
    | zero => rw [hB0]; exact bot_le
    | succ n ih => rw [hBs (n + 1), hBs n]; exact sup_le_sup_left (Submodule.map_mono ih) _
  have hstep : ∀ m, B (m + 2) ≤ B (m + 1) → B (m + 1) ≤ B m := by
    intro m hm u hu
    have hxu' : x * u ∈ B (m + 2) := by
      rw [hBs (m + 1)]
      exact Submodule.mem_sup_right ⟨u, hu, rfl⟩
    have hxu : x * u ∈ B (m + 1) := hm hxu'
    rw [hBs m] at hxu
    obtain ⟨k, hk, _, ⟨v, hv, rfl⟩, he⟩ := Submodule.mem_sup.mp hxu
    have hk0 : k = 0 := hKx k hk ⟨u - v, by
      change x * (u - v) = k
      rw [mul_sub, ← he]
      change k + x * v - x * v = k
      abel⟩
    subst hk0
    have huv : u - v = 0 := hx _ (by
      rw [mul_sub, ← he]
      change 0 + x * v - x * v = 0
      abel)
    rwa [sub_eq_zero.mp huv]
  have hdown : ∀ m, B (m + 1) ≤ B m → B 1 ≤ B 0 := by
    intro m
    induction m with
    | zero => exact id
    | succ m ih => exact fun h => ih (hstep m h)
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := Rᵐᵒᵖ) (M := R)).mpr
    inferInstance ⟨B, hmono⟩
  have h1 : B 1 ≤ B 0 := hdown n (hn (n + 1) (by omega)).symm.le
  have hyK : y ∈ B 1 := by rw [show (1 : ℕ) = 0 + 1 from rfl, hBs 0]; exact Submodule.mem_sup_left ⟨1, mul_one y⟩
  exact hy ((Submodule.mem_bot _).mp (hB0 ▸ h1 hyK))

/-- In a simple right Noetherian ring an element with zero right annihilator
is regular. -/
theorem mem_nonZeroDivisors_of_rightAnn [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] {x : R}
    (hx : ∀ z : R, x * z = 0 → z = 0) : x ∈ R⁰ := by
  refine ⟨hx, fun z hzx => eq_zero_of_isEssential_rightAnn ?_⟩
  refine (isEssential_principal hx).mono ?_
  rintro _ ⟨r, rfl⟩
  change z * (x * r) = 0
  rw [← mul_assoc, hzx, zero_mul]

/-- **Goldie.** Every essential right ideal of a simple right Noetherian ring
contains a regular element. -/
theorem exists_mem_nonZeroDivisors_of_isEssential [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {E : Submodule Rᵐᵒᵖ R} (hE : IsEssential E) : ∃ s ∈ E, s ∈ R⁰ := by
  obtain ⟨x, hxE, hx⟩ := exists_mem_rightAnn_eq_bot hE
  exact ⟨x, hxE, mem_nonZeroDivisors_of_rightAnn hx⟩

/-- A right ideal containing a regular element is essential. -/
theorem isEssential_of_mem_nonZeroDivisors [IsNoetherian Rᵐᵒᵖ R]
    {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ∈ R⁰) : IsEssential I :=
  (isEssential_principal hs.1).mono (by
    rintro _ ⟨r, rfl⟩
    have := I.smul_mem (op r) hsI
    rwa [op_smul_eq_mul] at this)

/-- **Goldie (right Ore condition).** In a simple right Noetherian ring, for
every `a` and regular `s` there are `a'` and regular `s'` with `a s' = s a'`. -/
theorem exists_right_ore [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] (a : R) {s : R}
    (hs : s ∈ R⁰) : ∃ a' s' : R, s' ∈ R⁰ ∧ a * s' = s * a' := by
  obtain ⟨s', hs'F, hs'⟩ := exists_mem_nonZeroDivisors_of_isEssential
    ((isEssential_principal hs.1).comap a)
  obtain ⟨a', ha'⟩ := hs'F
  exact ⟨a', s', hs', ha'.symm⟩

/-- Finitely many right ideals, each containing a regular element, have a
common regular element. -/
theorem exists_mem_nonZeroDivisors_finset [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (I : ι → Submodule Rᵐᵒᵖ R)
    (hI : ∀ i ∈ s, ∃ x ∈ I i, x ∈ R⁰) : ∃ x ∈ R⁰, ∀ i ∈ s, x ∈ I i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Submonoid.one_mem _, by simp⟩
  | @insert i s _ ih =>
    obtain ⟨m, hm, hmI⟩ := ih fun j hj => hI j (Finset.mem_insert_of_mem hj)
    obtain ⟨n, hnI, hn⟩ := hI i (Finset.mem_insert_self i s)
    obtain ⟨a', s', hs', he⟩ := exists_right_ore n hm
    refine ⟨n * s', Submonoid.mul_mem _ hn hs', fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have := (I j).smul_mem (op s') hnI
      rwa [op_smul_eq_mul] at this
    · rw [he]
      have := (I j).smul_mem (op a') (hmI j hj)
      rwa [op_smul_eq_mul] at this

/-- A right ideal containing a regular element: every `f` has a regular `b`
with `f b ∈ I` (the quotient `R/I` is Goldie-torsion). -/
theorem exists_mul_mem_of_mem_nonZeroDivisors [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    {I : Submodule Rᵐᵒᵖ R} {s : R} (hsI : s ∈ I) (hs : s ∈ R⁰) (f : R) :
    ∃ b ∈ R⁰, f * b ∈ I := by
  obtain ⟨a', s', hs', he⟩ := exists_right_ore f hs
  refine ⟨s', hs', ?_⟩
  rw [he]
  have := I.smul_mem (op a') hsI
  rwa [op_smul_eq_mul] at this

/-- Regularity in `Rᵐᵒᵖ` is regularity in `R`. -/
theorem op_mem_nonZeroDivisors_iff {x : R} : op x ∈ (Rᵐᵒᵖ)⁰ ↔ x ∈ R⁰ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun y hy => op_injective (h2 (op y) (unop_injective hy)),
      fun y hy => op_injective (h1 (op y) (unop_injective hy))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun y hy => unop_injective (h2 (unop y) (op_injective hy)),
      fun y hy => unop_injective (h1 (unop y) (op_injective hy))⟩

/-- **Goldie.** The regular elements of a simple right Noetherian ring form a
right Ore set; in Mathlib's left-handed convention, `(Rᵐᵒᵖ)⁰` is an Ore set of
`Rᵐᵒᵖ`, so the classical right quotient ring is the Ore localization of `Rᵐᵒᵖ`
at `(Rᵐᵒᵖ)⁰`. -/
theorem nonempty_oreSet_op [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R] :
    Nonempty (OreLocalization.OreSet (Rᵐᵒᵖ)⁰) := by
  refine OreLocalization.nonempty_oreSet_iff.mpr ⟨?_, ?_⟩
  · rintro r₁ r₂ ⟨s, hs⟩ he
    refine ⟨1, ?_⟩
    have hs' : unop s ∈ R⁰ := op_mem_nonZeroDivisors_iff.mp hs
    have h : unop s * (unop r₁ - unop r₂) = 0 := by
      rw [mul_sub, sub_eq_zero]
      exact congrArg unop he
    rw [unop_injective (sub_eq_zero.mp (hs'.1 _ h))]
  · rintro r ⟨s, hs⟩
    obtain ⟨a', s', hs', he⟩ := exists_right_ore (unop r)
      (op_mem_nonZeroDivisors_iff.mp hs)
    exact ⟨op a', ⟨op s', op_mem_nonZeroDivisors_iff.mpr hs'⟩, unop_injective he⟩

/-! ## A principal right ideal of full rank in every right ideal -/

/-- If `C` is maximal among right ideals with `I ⊓ C = ⊥`, then `I ⊔ C` is
essential. -/
theorem isEssential_sup_of_maximal {I C : Submodule Rᵐᵒᵖ R} (hIC : I ⊓ C = ⊥)
    (hmax : ∀ C', C ≤ C' → I ⊓ C' = ⊥ → C' = C) : IsEssential (I ⊔ C) := by
  intro y hy
  by_contra! h
  have hdisj : I ⊓ (C ⊔ principalRightIdeal y) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro z ⟨hzI, hz⟩
    obtain ⟨c, hc, _, ⟨r, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hz
    have hyr : y * r = 0 := by
      by_contra hne
      refine h r hne ?_
      have hsub : c + y * r - c ∈ I ⊔ C :=
        Submodule.sub_mem _ (Submodule.mem_sup_left hzI) (Submodule.mem_sup_right hc)
      rwa [add_sub_cancel_left] at hsub
    change c + y * r ∈ I at hzI
    change c + y * r = 0
    rw [hyr, add_zero] at hzI ⊢
    have : c ∈ I ⊓ C := ⟨hzI, hc⟩
    rwa [hIC] at this
  have heq := hmax _ le_sup_left hdisj
  have hyC : y ∈ C := heq ▸ Submodule.mem_sup_right ⟨1, mul_one y⟩
  exact h 1 (by rwa [mul_one]) (by rw [mul_one]; exact Submodule.mem_sup_right hyC)

/-- **Every right ideal has a principal right ideal of full rank.** In a
simple right Noetherian ring, every right ideal `I` contains an element `a`
such that `I / aR` is Goldie-torsion: every `y ∈ I` has a regular `s` with
`y s ∈ aR`. -/
theorem exists_mem_forall_exists_mul_mem [IsSimpleRing R] [IsNoetherian Rᵐᵒᵖ R]
    (I : Submodule Rᵐᵒᵖ R) :
    ∃ a ∈ I, ∀ y ∈ I, ∃ s ∈ R⁰, y * s ∈ principalRightIdeal a := by
  obtain ⟨C, hC, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := Rᵐᵒᵖ) (M := R)).mpr inferInstance
      {C | I ⊓ C = ⊥} ⟨⊥, inf_bot_eq _⟩
  have hE : IsEssential (I ⊔ C) := isEssential_sup_of_maximal hC fun C' hle hC' => by
    by_contra hne
    exact hmax C' hC' (lt_of_le_of_ne hle (Ne.symm hne))
  obtain ⟨s, hsE, hs⟩ := exists_mem_nonZeroDivisors_of_isEssential hE
  obtain ⟨a, haI, c, hcC, rfl⟩ := Submodule.mem_sup.mp hsE
  refine ⟨a, haI, fun y hyI => ?_⟩
  obtain ⟨t, ⟨r', hr'⟩, ht⟩ := exists_mem_nonZeroDivisors_of_isEssential
    ((isEssential_principal hs.1).comap y)
  change (a + c) * r' = y * t at hr'
  have hytI : y * t ∈ I := by
    have := I.smul_mem (op t) hyI
    rwa [op_smul_eq_mul] at this
  have harI : a * r' ∈ I := by
    have := I.smul_mem (op r') haI
    rwa [op_smul_eq_mul] at this
  have hcr : c * r' ∈ I ⊓ C := by
    refine ⟨?_, ?_⟩
    · have : c * r' = y * t - a * r' := by rw [← hr', add_mul, add_sub_cancel_left]
      rw [this]
      exact I.sub_mem hytI harI
    · have := C.smul_mem (op r') hcC
      rwa [op_smul_eq_mul] at this
  rw [hC, Submodule.mem_bot] at hcr
  refine ⟨t, ht, r', ?_⟩
  change a * r' = y * t
  rw [← hr', add_mul, hcr, add_zero]

end AlgebraicAnalysis.Goldie
