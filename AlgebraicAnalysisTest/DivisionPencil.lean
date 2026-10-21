module

public import AlgebraicAnalysis.LinearAlgebra.ActivatedPencil
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Concrete central-pencil oracles

The maps below are explicit two-by-two diagonal matrices, acting on coordinate
pairs. Their exceptional parameters are calculated directly from the two
coordinates, independently of the abstract finiteness proofs. A nilpotent
matrix also detects reversal of the activation composition.
-/

namespace DivisionPencilTest

variable {F : Type*} [Field F]

/-- The coordinate action of the matrix `diag(a,b)`. -/
def diag (a b : F) : (F × F) →ₗ[F] (F × F) where
  toFun x := (a * x.1, b * x.2)
  map_add' x y := by ext <;> simp [mul_add]
  map_smul' c x := by ext <;> simp [mul_left_comm]

@[simp] theorem diag_apply (a b : F) (x : F × F) :
    diag a b x = (a * x.1, b * x.2) := rfl

/-- Direct matrix oracle: `diag(a,b)` is injective exactly when both diagonal
entries are nonzero. Necessity uses the two standard coordinate vectors. -/
theorem diag_injective_iff (a b : F) :
    Function.Injective (diag a b) ↔ a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro h
    constructor
    · intro ha
      have := h (show diag a b (1, 0) = diag a b (0, 0) by simp [ha])
      exact one_ne_zero (congrArg Prod.fst this)
    · intro hb
      have := h (show diag a b (0, 1) = diag a b (0, 0) by simp [hb])
      exact one_ne_zero (congrArg Prod.snd this)
  · rintro ⟨ha, hb⟩ x y hxy
    exact Prod.ext
      (mul_left_cancel₀ ha (congrArg Prod.fst hxy))
      (mul_left_cancel₀ hb (congrArg Prod.snd hxy))

/-- `P=diag(1,0)`, `Q=diag(1,1)`, `T=diag(0,1)` is activated. -/
theorem diag_activation : (diag (0 : F) 1).comp (diag 1 0) = 0 := by
  ext <;> simp

theorem diag_joint_injective :
    Function.Injective (fun x : F × F => (diag 1 0 x, diag 0 1 (diag 1 1 x))) := by
  intro x y h
  exact Prod.ext (by simpa using congrArg (fun z => z.1.1) h)
    (by simpa using congrArg (fun z => z.2.2) h)

/-- The two exceptional scalars of this activated pencil, computed by coordinates. -/
theorem diag_activated_bad_iff (c : F) :
    (¬ Function.Injective (fun x : F × F => diag 1 0 x + c • diag 1 1 x)) ↔
      c = 0 ∨ c = -1 := by
  have heq : (fun x : F × F => diag 1 0 x + c • diag 1 1 x) = diag (1 + c) c := by
    funext x
    ext <;> simp [add_mul]
  rw [heq, diag_injective_iff, not_and_or]
  simp only [ne_eq, not_not]
  constructor
  · rintro (h | h)
    · exact Or.inr (eq_neg_of_add_eq_zero_right h)
    · exact Or.inl h
  · rintro (rfl | rfl) <;> simp

/-- Ordinary-pencil oracle: `I + c diag(1,-1)` has exceptional scalars `-1,1`. -/
theorem diag_ordinary_bad_iff (c : ℚ) :
    (¬ Function.Injective (fun x : ℚ × ℚ => x + c • diag 1 (-1) x)) ↔
      c = -1 ∨ c = 1 := by
  have heq : (fun x : ℚ × ℚ => x + c • diag 1 (-1) x) = diag (1 + c) (1 - c) := by
    funext x
    ext <;> simp [add_mul, sub_eq_add_neg]
  rw [heq, diag_injective_iff, not_and_or]
  constructor
  · rintro (h | h)
    · exact Or.inl (by have h := not_not.mp h; linarith)
    · exact Or.inr (by have h := not_not.mp h; linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- API check over a field of positive characteristic. -/
example :
    {c : ZMod 3 | ¬ Function.Injective
      (fun x : ZMod 3 × ZMod 3 => diag 1 0 x + c • diag 1 1 x)}.Finite :=
  AlgebraicAnalysis.activated_pencil_finite (RingHom.id (ZMod 3)) (fun _ _ => mul_comm _ _)
    (diag (1 : ZMod 3) 0) (diag 1 1) (diag 0 1) diag_activation diag_joint_injective

example : ¬ Function.Injective
    (fun x : ZMod 3 × ZMod 3 => diag 1 0 x + (2 : ZMod 3) • diag 1 1 x) := by
  rw [diag_activated_bad_iff]
  right
  decide

example : Function.Injective
    (fun x : ZMod 3 × ZMod 3 => diag 1 0 x + (1 : ZMod 3) • diag 1 1 x) := by
  by_contra h
  have := (diag_activated_bad_iff (1 : ZMod 3)).mp h
  rcases this with h | h <;> revert h <;> decide

/-- API check for the ordinary-pencil extraction. -/
example : {c : ℚ | ∃ x : ℚ × ℚ, x ≠ 0 ∧ x + c • diag 1 (-1) x = 0}.Finite :=
  AlgebraicAnalysis.pencil_ker_finite (RingHom.id ℚ) (fun _ _ => mul_comm _ _)
    (LinearMap.id : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)) (diag (1 : ℚ) (-1)) Function.injective_id

/-- The matrix `[[0,0],[1,0]]`. -/
def lowerShift : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) :=
  (0 : (ℚ × ℚ) →ₗ[ℚ] ℚ).prod (LinearMap.fst ℚ ℚ ℚ)

/-- The matrix `[[0,1],[0,0]]`. -/
def upperShift : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) :=
  (LinearMap.snd ℚ ℚ ℚ).prod (0 : (ℚ × ℚ) →ₗ[ℚ] ℚ)

/-- Reversing the composition hypothesis is insufficient: `P ∘ T = 0`. -/
example : (diag (1 : ℚ) 0).comp lowerShift = 0 := by
  ext <;> simp [lowerShift]

example : Function.Injective
    (fun x : ℚ × ℚ => (diag 1 0 x, lowerShift (upperShift x))) := by
  intro x y h
  exact Prod.ext (by simpa using congrArg (fun z => z.1.1) h)
    (by simpa [lowerShift, upperShift] using congrArg (fun z => z.2.2) h)

/-- Every parameter is bad with the reversed composition, witnessed by `(-c,1)`. -/
theorem reversed_activation_not_injective (c : ℚ) :
    ¬ Function.Injective (fun x : ℚ × ℚ => diag 1 0 x + c • upperShift x) := by
  intro h
  have heq : diag 1 0 (-c, 1) + c • upperShift (-c, 1) =
      diag 1 0 (0, 0) + c • upperShift (0, 0) := by
    ext <;> simp [upperShift]
  have := congrArg Prod.snd (h heq)
  norm_num at this

end DivisionPencilTest
