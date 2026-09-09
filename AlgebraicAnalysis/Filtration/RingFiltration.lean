import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.RingTheory.Finiteness.Subalgebra

/-!
# Ascending ring filtrations

This file defines the generic ascending filtration of a (possibly
noncommutative) ring `A` over a commutative base ring `R`, and develops the
foundational closure, associated-graded, order, and finiteness API that the
rest of a filtered-ring / D-module layer sits on.

The pinned Mathlib has two filtration-shaped structures which do not cover
this notion: `Ideal.Filtration` (`Mathlib.RingTheory.Filtration`) is a
*decreasing* `I`-adic filtration of a module over a fixed ideal `I`, and
`IsRingFiltration`/`IsFiltration` (`Mathlib.RingTheory.FilteredAlgebra.Basic`)
are `SetLike`-generic classes that do not require a multiplicative unit in
degree `0` or exhaustiveness, and are stated for an arbitrary `Preorder`
index rather than for the specific `ℕ`-indexed, submodule-multiplication
shape used here. Neither is reused as the primary structure; both are noted
so a later contributor does not duplicate the search. What *is* reused is
Mathlib's submodule-multiplication semiring structure on `Submodule R A`
(`Mathlib.Algebra.Algebra.Operations`, available for `[CommSemiring R]
[Semiring A] [Algebra R A]`) and the quotient-bilinear-form lifting lemma
`LinearMap.liftQ₂` (`Mathlib.LinearAlgebra.Quotient.Bilinear`), which is
exactly the well-definedness tool the associated-graded multiplication needs.

## Main definitions

* `RingFiltration R A`: an ascending, exhaustive, unital, submultiplicative
  family `F : ℕ → Submodule R A`.
* `RingFiltration.GradedQuotient φ i`: the graded piece `F i / F (i - 1)`
  (with the convention `F (-1) = ⊥`), together with `RingFiltration.gradedMul`,
  the well-defined multiplication `Graded i → Graded j → Graded (i + j)`
  induced on representatives.
* `RingFiltration.order`: for `a ≠ 0`, the least filtration degree containing
  `a`.
* `RingFiltration.Separated`: no oscillation — once two consecutive filtration
  pieces coincide, the filtration stays constant from there on.
* `RingFiltration.IsGoodFiltration`: each piece is a finite `R`-module; the
  hypothesis a later Hilbert-function argument needs. Proved closed under sup
  and product of pieces.

No Weyl algebra, differential operator, or other application-specific
structure appears in this file.
-/

namespace AlgebraicAnalysis

/-- An ascending filtration of a ring `A` by `R`-submodules: monotone,
containing `1` in degree `0`, submultiplicative (`F i * F j ≤ F (i + j)`,
using the submodule-multiplication semiring structure on `Submodule R A`),
and exhaustive (`⨆ i, F i = ⊤`). -/
structure RingFiltration (R A : Type*) [CommRing R] [Ring A] [Algebra R A] where
  /-- The filtration pieces. -/
  F : ℕ → Submodule R A
  /-- The pieces are increasing. -/
  mono : Monotone F
  /-- The unit lies in degree `0`. -/
  one_mem : (1 : A) ∈ F 0
  /-- Submultiplicativity: `F i * F j ⊆ F (i + j)`. -/
  mul_le : ∀ i j, F i * F j ≤ F (i + j)
  /-- The filtration exhausts the ring. -/
  exhaustive : ⨆ i, F i = ⊤

namespace RingFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (φ : RingFiltration R A)

/-! ## Basic closure facts -/

/-- A product of elements of filtration degree `i` and `j` has filtration
degree at most `i + j`. -/
theorem mul_mem_add {a b : A} {i j : ℕ} (ha : a ∈ φ.F i) (hb : b ∈ φ.F j) :
    a * b ∈ φ.F (i + j) :=
  φ.mul_le i j (Submodule.mul_mem_mul ha hb)

/-- A power `a ^ n` of an element of filtration degree `d` has filtration
degree at most `d * n`. -/
theorem pow_mem {a : A} {d : ℕ} (ha : a ∈ φ.F d) (n : ℕ) : a ^ n ∈ φ.F (d * n) := by
  induction n with
  | zero => simpa using φ.one_mem
  | succ n ih =>
      have hstep : a ^ n * a ∈ φ.F (d * n + d) := φ.mul_mem_add ih ha
      simpa [pow_succ, Nat.mul_succ] using hstep

/-! ## The associated graded pieces -/

/-- The predecessor filtration piece, with the convention `F (-1) = ⊥` used
at degree `0`. -/
def below : ℕ → Submodule R A
  | 0 => ⊥
  | i + 1 => φ.F i

@[simp] theorem below_zero : φ.below 0 = ⊥ := rfl

theorem below_succ (i : ℕ) : φ.below (i + 1) = φ.F i := rfl

/-- The predecessor piece, viewed as a submodule of `F i` itself. -/
def belowInF (i : ℕ) : Submodule R (φ.F i) :=
  (φ.below i).comap (φ.F i).subtype

theorem mem_belowInF {i : ℕ} {x : φ.F i} : x ∈ φ.belowInF i ↔ (x : A) ∈ φ.below i :=
  Iff.rfl

/-- The `i`-th graded piece `F i / F (i - 1)` of the associated graded
module, with `F (-1) = ⊥` at `i = 0`. -/
abbrev GradedQuotient (i : ℕ) : Type _ := φ.F i ⧸ φ.belowInF i

/-- `below i * F j ≤ below (i + j)`: multiplying a below-degree-`i` element
by a degree-`j` element lands below degree `i + j`. -/
theorem below_mul_le (i j : ℕ) : φ.below i * φ.F j ≤ φ.below (i + j) := by
  cases i with
  | zero => simp
  | succ n =>
      have heq : n + 1 + j = n + j + 1 := by omega
      rw [below_succ, heq, below_succ]
      exact φ.mul_le n j

/-- `F i * below j ≤ below (i + j)`: multiplying a degree-`i` element by a
below-degree-`j` element lands below degree `i + j`. -/
theorem mul_below_le (i j : ℕ) : φ.F i * φ.below j ≤ φ.below (i + j) := by
  cases j with
  | zero => simp
  | succ n =>
      have heq : i + (n + 1) = i + n + 1 := by omega
      rw [below_succ, heq, below_succ]
      exact φ.mul_le i n

/-- Multiplication of representatives, landing directly in the graded
quotient of the sum degree. This is *not yet* shown to be well defined on
the graded pieces; see `gradedMul` for the induced, well-defined product. -/
def repMul (i j : ℕ) : φ.F i →ₗ[R] φ.F j →ₗ[R] φ.GradedQuotient (i + j) :=
  LinearMap.mk₂' R R
    (fun a b => Submodule.Quotient.mk
      ⟨(a : A) * (b : A), φ.mul_mem_add a.2 b.2⟩)
    (fun a₁ a₂ b => by
      rw [← Submodule.Quotient.mk_add]
      congr 1
      exact Subtype.ext (by simp [add_mul]))
    (fun c a b => by
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      exact Subtype.ext (by simp))
    (fun a b₁ b₂ => by
      rw [← Submodule.Quotient.mk_add]
      congr 1
      exact Subtype.ext (by simp [mul_add]))
    (fun c a b => by
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      exact Subtype.ext (by simp))

theorem repMul_apply (i j : ℕ) (a : φ.F i) (b : φ.F j) :
    φ.repMul i j a b =
      Submodule.Quotient.mk (p := φ.belowInF (i + j))
        ⟨(a : A) * (b : A), φ.mul_mem_add a.2 b.2⟩ :=
  rfl

/-- Changing the first representative by a below-degree-`i` element does not
change `repMul`. -/
theorem belowInF_le_repMul_ker (i j : ℕ) :
    φ.belowInF i ≤ (φ.repMul i j).ker := by
  intro x hx
  have hx' : (x : A) ∈ φ.below i := φ.mem_belowInF.1 hx
  refine LinearMap.mem_ker.mpr (LinearMap.ext fun y => ?_)
  show Submodule.Quotient.mk (p := φ.belowInF (i + j)) _ = (0 : φ.GradedQuotient (i + j))
  rw [Submodule.Quotient.mk_eq_zero]
  exact φ.mem_belowInF.2 (φ.below_mul_le i j (Submodule.mul_mem_mul hx' y.2))

/-- Changing the second representative by a below-degree-`j` element does not
change `repMul`. -/
theorem belowInF_le_repMul_flip_ker (i j : ℕ) :
    φ.belowInF j ≤ (φ.repMul i j).flip.ker := by
  intro y hy
  have hy' : (y : A) ∈ φ.below j := φ.mem_belowInF.1 hy
  refine LinearMap.mem_ker.mpr (LinearMap.ext fun x => ?_)
  show Submodule.Quotient.mk (p := φ.belowInF (i + j)) _ = (0 : φ.GradedQuotient (i + j))
  rw [Submodule.Quotient.mk_eq_zero]
  exact φ.mem_belowInF.2 (φ.mul_below_le i j (Submodule.mul_mem_mul x.2 hy'))

/-- The well-defined multiplication `Graded i → Graded j → Graded (i + j)` on
the associated graded module, induced from `repMul` on representatives. This
is where the submultiplicativity hypothesis `mul_le` is genuinely used to
show a *well-defined* map, not merely assumed. -/
def gradedMul (i j : ℕ) :
    φ.GradedQuotient i →ₗ[R] φ.GradedQuotient j →ₗ[R] φ.GradedQuotient (i + j) :=
  LinearMap.liftQ₂ (φ.belowInF i) (φ.belowInF j) (φ.repMul i j)
    (φ.belowInF_le_repMul_ker i j) (φ.belowInF_le_repMul_flip_ker i j)

@[simp] theorem gradedMul_mk (i j : ℕ) (a : φ.F i) (b : φ.F j) :
    φ.gradedMul i j (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (p := φ.belowInF (i + j))
        ⟨(a : A) * (b : A), φ.mul_mem_add a.2 b.2⟩ :=
  rfl

/-! ## The order function -/

theorem exists_mem_of_directed (a : A) : ∃ i, a ∈ φ.F i := by
  have ha : a ∈ (⊤ : Submodule R A) := Submodule.mem_top
  rw [← φ.exhaustive] at ha
  exact (Submodule.mem_iSup_of_directed φ.F φ.mono.directed_le).mp ha

open scoped Classical

/-- The order of a nonzero element `a`: the least filtration degree
containing it. Well defined by exhaustiveness of the filtration. -/
noncomputable def order {a : A} (_ha : a ≠ 0) : ℕ :=
  Nat.find (φ.exists_mem_of_directed a)

theorem mem_order {a : A} (ha : a ≠ 0) : a ∈ φ.F (φ.order ha) :=
  Nat.find_spec (φ.exists_mem_of_directed a)

theorem order_le {a : A} (ha : a ≠ 0) {i : ℕ} (hi : a ∈ φ.F i) : φ.order ha ≤ i :=
  Nat.find_min' (φ.exists_mem_of_directed a) hi

/-- The order of a product is at most the sum of the orders. -/
theorem order_mul_le {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b ≠ 0) :
    φ.order hab ≤ φ.order ha + φ.order hb :=
  φ.order_le hab (φ.mul_mem_add (φ.mem_order ha) (φ.mem_order hb))

/-- The order of a sum is at most the maximum of the orders. -/
theorem order_add_le {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    φ.order hab ≤ max (φ.order ha) (φ.order hb) := by
  refine φ.order_le hab (add_mem ?_ ?_)
  · exact φ.mono (le_max_left _ _) (φ.mem_order ha)
  · exact φ.mono (le_max_right _ _) (φ.mem_order hb)

/-! ## Separated filtrations and the finiteness hypothesis -/

/-- A filtration is separated when it does not oscillate: once two
consecutive pieces coincide, the filtration stays constant from there on
(equivalently, `F` is strictly increasing until it stabilises). -/
def Separated (φ : RingFiltration R A) : Prop :=
  ∀ i, φ.F i = φ.F (i + 1) → ∀ j, i ≤ j → φ.F j = φ.F i

/-- A submodule sup of two finite `R`-modules in an `R`-algebra is finite.
Generic fact about `Submodule R A`, not specific to a filtration. -/
theorem finite_sup {p q : Submodule R A} (hp : Module.Finite R p) (hq : Module.Finite R q) :
    Module.Finite R (↥(p ⊔ q)) :=
  Module.Finite.iff_fg.mpr
    (Submodule.FG.sup (Module.Finite.iff_fg.mp hp) (Module.Finite.iff_fg.mp hq))

/-- A submodule product of two finite `R`-modules in an `R`-algebra is
finite. Generic fact about `Submodule R A`, not specific to a filtration. -/
theorem finite_mul {p q : Submodule R A} (hp : Module.Finite R p) (hq : Module.Finite R q) :
    Module.Finite R (p * q) :=
  Module.Finite.iff_fg.mpr
    (Submodule.FG.mul (Module.Finite.iff_fg.mp hp) (Module.Finite.iff_fg.mp hq))

/-- A good filtration: each piece is a finite `R`-module. This is exactly
the finite-dimensionality hypothesis a later Hilbert-function / Bernstein-type
argument needs; it is not derivable from the ascending-exhaustive-unital-
submultiplicative axioms alone (e.g. `A` itself may fail to be Noetherian
over `R`), so it is recorded as an explicit class. -/
class IsGoodFiltration (φ : RingFiltration R A) : Prop where
  /-- Every filtration piece is a finite `R`-module. -/
  finite : ∀ i, Module.Finite R (φ.F i)

theorem IsGoodFiltration.finite_sup [h : φ.IsGoodFiltration] (i j : ℕ) :
    Module.Finite R (↥(φ.F i ⊔ φ.F j)) :=
  RingFiltration.finite_sup (h.finite i) (h.finite j)

theorem IsGoodFiltration.finite_mul [h : φ.IsGoodFiltration] (i j : ℕ) :
    Module.Finite R (φ.F i * φ.F j) :=
  RingFiltration.finite_mul (h.finite i) (h.finite j)

end RingFiltration

end AlgebraicAnalysis
