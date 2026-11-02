module
public import AlgebraicAnalysis.Filtration.SymbolNoetherian
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

/-!
# Opposite filtrations and opposite symbols

For a ring filtration `φ` of an `R`-algebra `A`, `φ.opposite` is the filtration
of `Aᵐᵒᵖ` whose piece `n` is the image of `φ.F n` under `a ↦ op a`. A symbol
`S : φ.GradedSymbol 𝒜` induces `S.opposite : φ.opposite.GradedSymbol 𝒜` with the
same graded algebra `G`. This uses only that `G` is commutative: the product
`op y * op x = op (x * y)` of opposite elements has symbol `gr j(y) · gr i(x)`,
which is the product `gr i(x) · gr j(y)` in `G`.

Right ideals of `Aᵐᵒᵖ` are left ideals of `A`, and left ideals of `Aᵐᵒᵖ` are
right ideals of `A` (`rightIdealOpEquiv`, `leftIdealOpEquiv`). Deviation and
Noetherianity are order-theoretic, so each right-side statement about `Aᵐᵒᵖ`
is equivalent to the left-side statement about `A`, and conversely
(`isNoetherian_right_op_iff`, `devLE_right_op_iff`, `isNoetherianRing_op_iff`,
`devLE_left_op_iff`). The module `AlgebraicAnalysis.Filtration.SymbolNoetherian`
uses these to transport its conclusions to the opposite symbol.

## Main definitions and results

* `RingFiltration.opposite φ`: the opposite filtration of `Aᵐᵒᵖ`.
* `RingFiltration.GradedSymbol.opposite S`: the opposite symbol, with the same `G`.
* `RingFiltration.GradedSymbol.coe_gr_opposite`: the opposite symbol of `op u` is
  the symbol of `u`.
* `rightIdealOpEquiv`, `leftIdealOpEquiv`: the order isomorphisms of ideal lattices.
-/

namespace AlgebraicAnalysis

open MulOpposite

section Ideals

variable (A : Type*) [Ring A]

/-- Right ideals of `Aᵐᵒᵖ` correspond to left ideals of `A`: `x` lies in the
left ideal iff `op x` lies in the right ideal. -/
def rightIdealOpEquiv : Submodule Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ ≃o Submodule A A where
  toFun p :=
    { carrier := {x | op x ∈ p}
      add_mem' := fun {x y} hx hy => by
        simpa [op_add] using p.add_mem hx hy
      zero_mem' := by simp
      smul_mem' := fun c {x} hx => by
        change op (c * x) ∈ p
        rw [op_mul, ← op_smul_eq_mul]
        exact p.smul_mem _ hx }
  invFun q :=
    { carrier := {y | unop y ∈ q}
      add_mem' := fun {y z} hy hz => by
        simpa [unop_add] using q.add_mem hy hz
      zero_mem' := by simp
      smul_mem' := fun c {y} hy => by
        obtain ⟨z⟩ := c
        obtain ⟨a⟩ := z
        change unop (op (op a) • y) ∈ q
        rw [op_smul_eq_mul, unop_mul, unop_op]
        exact q.smul_mem a hy }
  left_inv p := by
    ext y
    simp
  right_inv q := by
    ext x
    simp
  map_rel_iff' := by
    intro p q
    constructor
    · intro h y hy
      have h' : unop y ∈ ({x | op x ∈ p} : Set A) := by simpa using hy
      simpa using h h'
    · intro h x hx
      exact h hx

/-- Left ideals of `Aᵐᵒᵖ` correspond to right ideals of `A`: `x` lies in the
right ideal iff `op x` lies in the left ideal. -/
def leftIdealOpEquiv : Submodule Aᵐᵒᵖ Aᵐᵒᵖ ≃o Submodule Aᵐᵒᵖ A where
  toFun p :=
    { carrier := {x | op x ∈ p}
      add_mem' := fun {x y} hx hy => by
        simpa [op_add] using p.add_mem hx hy
      zero_mem' := by simp
      smul_mem' := fun c {x} hx => by
        obtain ⟨a⟩ := c
        change op (x * a) ∈ p
        rw [op_mul, ← smul_eq_mul]
        exact p.smul_mem _ hx }
  invFun q :=
    { carrier := {y | unop y ∈ q}
      add_mem' := fun {y z} hy hz => by
        simpa [unop_add] using q.add_mem hy hz
      zero_mem' := by simp
      smul_mem' := fun c {y} hy => by
        change unop (c * y) ∈ q
        rw [unop_mul]
        exact q.smul_mem c hy }
  left_inv p := by
    ext y
    simp
  right_inv q := by
    ext x
    simp
  map_rel_iff' := by
    intro p q
    constructor
    · intro h y hy
      have h' : unop y ∈ ({x | op x ∈ p} : Set A) := by simpa using hy
      simpa using h h'
    · intro h x hx
      exact h hx

end Ideals

namespace RingFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The opposite map `A →ₗ[R] Aᵐᵒᵖ`, `a ↦ op a`. -/
abbrev opLin (R A : Type*) [CommRing R] [Ring A] [Algebra R A] : A →ₗ[R] Aᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).toLinearMap

/-- The opposite filtration of `Aᵐᵒᵖ`: piece `n` is the image of `φ.F n` under
`a ↦ op a`. -/
def opposite (φ : RingFiltration R A) : RingFiltration R Aᵐᵒᵖ where
  F n := (φ.F n).map (opLin R A)
  mono _ _ hij := Submodule.map_mono (φ.mono hij)
  one_mem := Submodule.mem_map.mpr ⟨1, φ.one_mem, by simp [opLin]⟩
  mul_le i j := by
    show (φ.F i).map (opLin R A) * (φ.F j).map (opLin R A) ≤ (φ.F (i + j)).map (opLin R A)
    rw [← Submodule.map_op_mul, add_comm i j]
    exact Submodule.map_mono (φ.mul_le j i)
  exhaustive := by
    rw [← Submodule.map_iSup, φ.exhaustive, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (MulOpposite.opLinearEquiv R).surjective

theorem mem_opposite_op_iff {φ : RingFiltration R A} {n : ℕ} {a : A} :
    op a ∈ (φ.opposite).F n ↔ a ∈ φ.F n := by
  constructor
  · intro h
    obtain ⟨b, hb, hba⟩ := Submodule.mem_map.mp h
    have : b = a := by simpa [opLin] using hba
    exact this ▸ hb
  · intro h
    exact Submodule.mem_map_of_mem (f := opLin R A) h

theorem mem_opposite_iff {φ : RingFiltration R A} {n : ℕ} {x : Aᵐᵒᵖ} :
    x ∈ (φ.opposite).F n ↔ unop x ∈ φ.F n := by
  rw [← mem_opposite_op_iff (a := unop x), op_unop]

theorem mem_opposite_below_iff {φ : RingFiltration R A} (n : ℕ) (x : Aᵐᵒᵖ) :
    x ∈ (φ.opposite).below n ↔ unop x ∈ φ.below n := by
  cases n with
  | zero =>
    rw [below_zero, below_zero, Submodule.mem_bot, Submodule.mem_bot, unop_eq_zero_iff]
  | succ n =>
    rw [below_succ, below_succ]
    exact mem_opposite_iff

end RingFiltration

namespace RingFiltration.GradedSymbol

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing G] [Algebra R G]
variable {φ : RingFiltration R A} {𝒜 : ℕ → Submodule R G} (S : GradedSymbol φ 𝒜)

/-- The restriction of `unop` to the `n`-th piece of the opposite filtration. -/
def unopPiece (φ : RingFiltration R A) (n : ℕ) : (φ.opposite).F n →ₗ[R] φ.F n :=
  LinearMap.restrict ((MulOpposite.opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm :
      Aᵐᵒᵖ →ₗ[R] A) fun _ hx => mem_opposite_iff.mp hx

theorem unopPiece_apply (n : ℕ) (x : (φ.opposite).F n) :
    ((unopPiece φ n x : φ.F n) : A) = unop (x : Aᵐᵒᵖ) := rfl

/-- The opposite symbol: the symbol of `unop x` in the original filtration. -/
def opposite : GradedSymbol φ.opposite 𝒜 where
  gr n := S.gr n ∘ₗ unopPiece φ n
  gr_surjective n g := by
    obtain ⟨y, hy⟩ := S.gr_surjective n g
    have hx : op (y : A) ∈ (φ.opposite).F n := mem_opposite_op_iff.mpr y.2
    refine ⟨⟨op (y : A), hx⟩, ?_⟩
    have hy' : unopPiece φ n ⟨op (y : A), hx⟩ = y := Subtype.ext (unop_op _)
    change S.gr n (unopPiece φ n ⟨op (y : A), hx⟩) = g
    rw [hy', hy]
  gr_eq_zero_iff n x := by
    change S.gr n (unopPiece φ n x) = 0 ↔ (x : Aᵐᵒᵖ) ∈ (φ.opposite).below n
    rw [S.gr_eq_zero_iff]
    exact (mem_opposite_below_iff n (x : Aᵐᵒᵖ)).symm
  gr_mul i j x y := by
    have key : ∀ {n : ℕ} (z : (φ.opposite).F n),
        (((S.gr n ∘ₗ unopPiece φ n) z : 𝒜 n) : G) = S.grAt n (unop (z : Aᵐᵒᵖ)) := by
      intro n z
      rw [S.grAt_of_mem (mem_opposite_iff.mp z.2)]
      rfl
    rw [key, key, key]
    show S.grAt (i + j) (unop ((x : Aᵐᵒᵖ) * (y : Aᵐᵒᵖ))) = _
    rw [unop_mul]
    exact (S.grAt_mul' (add_comm j i) (mem_opposite_iff.mp y.2)
      (mem_opposite_iff.mp x.2)).trans (mul_comm _ _)

/-- The degree-`n` symbol of the opposite is the degree-`n` symbol of `unop x`. -/
theorem coe_gr_opposite {n : ℕ} (x : (φ.opposite).F n) :
    ((S.opposite.gr n x : 𝒜 n) : G) = S.grAt n (unop (x : Aᵐᵒᵖ)) := by
  rw [S.grAt_of_mem (mem_opposite_iff.mp x.2)]
  rfl

/-- The symbol of the opposite element `op u` is the symbol of `u`. -/
theorem grAt_opposite (n : ℕ) (u : A) : S.opposite.grAt n (op u) = S.grAt n u := by
  by_cases h : u ∈ φ.F n
  · rw [S.opposite.grAt_of_mem (mem_opposite_op_iff.mpr h), S.grAt_of_mem h]
    rfl
  · have h' : op u ∉ (φ.opposite).F n := fun h'' => h (mem_opposite_op_iff.mp h'')
    simp [grAt, h, h']

end RingFiltration.GradedSymbol


section Transport

variable (A : Type*) [Ring A]

/-- Right Noetherianity of `Aᵐᵒᵖ` is left Noetherianity of `A`. -/
theorem isNoetherian_right_op_iff : IsNoetherian Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ ↔ IsNoetherianRing A := by
  rw [isNoetherian_iff, IsNoetherianRing, isNoetherian_iff]
  exact ⟨fun _ => (rightIdealOpEquiv A).symm.strictMono.wellFoundedGT,
    fun _ => (rightIdealOpEquiv A).strictMono.wellFoundedGT⟩

/-- Left Noetherianity of `Aᵐᵒᵖ` is right Noetherianity of `A`. -/
theorem isNoetherianRing_op_iff : IsNoetherianRing Aᵐᵒᵖ ↔ IsNoetherian Aᵐᵒᵖ A := by
  rw [IsNoetherianRing, isNoetherian_iff, isNoetherian_iff]
  exact ⟨fun _ => (leftIdealOpEquiv A).symm.strictMono.wellFoundedGT,
    fun _ => (leftIdealOpEquiv A).strictMono.wellFoundedGT⟩

/-- Right deviation of `Aᵐᵒᵖ` is left deviation of `A`. -/
theorem devLE_right_op_iff (m : ℕ) : Module.DevLE Aᵐᵒᵖᵐᵒᵖ m Aᵐᵒᵖ ↔ Module.DevLE A m A :=
  Order.devLE_orderIso_iff m (rightIdealOpEquiv A)

/-- Left deviation of `Aᵐᵒᵖ` is right deviation of `A`. -/
theorem devLE_left_op_iff (m : ℕ) : Module.DevLE Aᵐᵒᵖ m Aᵐᵒᵖ ↔ Module.DevLE Aᵐᵒᵖ m A :=
  Order.devLE_orderIso_iff m (leftIdealOpEquiv A)

end Transport



namespace RingFiltration.GradedSymbol

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing G] [Algebra R G]
variable {φ : RingFiltration R A} {𝒜 : ℕ → Submodule R G} [GradedAlgebra 𝒜]
variable (S : RingFiltration.GradedSymbol φ 𝒜)

include S in
/-- **Right side of `Aᵐᵒᵖ` is the left side of `A`.** If `gr A` is a commutative
Noetherian ring, the right Noetherianity of the opposite symbol is the left
Noetherianity of `A`. -/
theorem isNoetherianRing_of_opposite_right [IsNoetherianRing G] : IsNoetherianRing A :=
  (isNoetherian_right_op_iff A).mp S.opposite.isNoetherian_right

include S in
/-- **Left side of `Aᵐᵒᵖ` is the right side of `A`.** -/
theorem isNoetherian_right_of_opposite_left [IsNoetherianRing G] :
    IsNoetherian Aᵐᵒᵖ A :=
  (isNoetherianRing_op_iff A).mp S.opposite.isNoetherianRing

include S in
/-- **Deviation of the right side of `Aᵐᵒᵖ` is the left deviation of `A`.** -/
theorem devLE_left_of_opposite_right [IsNoetherianRing G] (m : ℕ)
    (hm : ringKrullDim G ≤ m) : Module.DevLE A m A :=
  (devLE_right_op_iff A m).mp (S.opposite.devLE_right m hm)

include S in
/-- **Deviation of the left side of `Aᵐᵒᵖ` is the right deviation of `A`.** -/
theorem devLE_right_of_opposite_left [IsNoetherianRing G] (m : ℕ)
    (hm : ringKrullDim G ≤ m) : Module.DevLE Aᵐᵒᵖ m A :=
  (devLE_left_op_iff A m).mp (S.opposite.devLE_left m hm)

end RingFiltration.GradedSymbol

end AlgebraicAnalysis
