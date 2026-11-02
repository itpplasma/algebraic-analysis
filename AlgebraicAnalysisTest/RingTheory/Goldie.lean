module
public import AlgebraicAnalysis.RingTheory.Goldie.QuotientRing
public import AlgebraicAnalysis.RingTheory.Goldie.Torsion

@[expose] public section

/-!
# Concrete oracles for Goldie theory

The ring `M₂(ℚ)` of rational `2 × 2` matrices is simple and right Noetherian
but not a domain. The idempotent `e₁₁` is a zero divisor; a hand computation
shows that `R / e₁₁R` is not Goldie-torsion, so the regular-element hypothesis
of `isGoldieTorsion_quotient` cannot be dropped, while `e₁₁R / e₁₁R` is.
Goldie's theorem is instantiated at `M₂(ℚ)` with the Ore structure produced by
`nonempty_oreSet_oppositeSubmonoid`. For the field `ℚ` the Ore structure is
Mathlib's commutative one, so the results are used with an Ore structure not
built from Goldie's theorem; a direct computation (every nonzero fraction is a
unit) gives length one for the quotient ring, in agreement with the
finiteness and positivity proved for all simple right Noetherian rings.
-/

namespace AlgebraicAnalysisTest.Goldie

noncomputable section

open AlgebraicAnalysis AlgebraicAnalysis.Goldie AlgebraicAnalysis.DenominatorTorsion
open MulOpposite nonZeroDivisors

/-- `x ↦ op x` identifies `R`, as a right module over itself, with the left
regular module of `Rᵐᵒᵖ`. -/
def opRegularEquiv (R : Type*) [Ring R] : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ where
  toFun := op
  invFun := unop
  map_add' _ _ := rfl
  map_smul' c x := by
    change op (x * unop c) = c * op x
    rw [op_mul, op_unop]
  left_inv _ := rfl
  right_inv _ := rfl

theorem isNoetherian_of_isNoetherianRing_op (R : Type*) [Ring R] [IsNoetherianRing Rᵐᵒᵖ] :
    IsNoetherian Rᵐᵒᵖ R :=
  isNoetherian_of_linearEquiv (opRegularEquiv R).symm

/-! ## The matrix ring `M₂(ℚ)` -/

abbrev M2 := Matrix (Fin 2) (Fin 2) ℚ

instance : IsNoetherian M2ᵐᵒᵖ M2 := isNoetherian_of_isNoetherianRing_op M2

instance : OreLocalization.OreSet (OreRightLocalization.oppositeSubmonoid M2⁰) :=
  (nonempty_oreSet_oppositeSubmonoid (R := M2)).some

def e11 : M2 := !![1, 0; 0, 0]
def e22 : M2 := !![0, 0; 0, 1]

theorem e22_mul_e11 : e22 * e11 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11, e22, Matrix.mul_apply, Fin.sum_univ_two]

theorem e22_mul_e11_mul (r : M2) : e22 * (e11 * r) = 0 := by
  rw [← mul_assoc, e22_mul_e11, zero_mul]

theorem e22_ne_zero : e22 ≠ 0 := by
  intro h
  have := congrFun (congrFun h 1) 1
  simp [e22] at this

/-- Hostile control: `R / e₁₁R` is not Goldie-torsion, because a regular `s`
killing the class of `1` would lie in `e₁₁R`, which is left-annihilated by
`e₂₂ ≠ 0`. -/
theorem not_isGoldieTorsion_quotient_e11 :
    ¬ IsGoldieTorsion M2 (M2 ⧸ principalRightIdeal e11) := by
  intro h
  obtain ⟨s, hs, hs1⟩ := h (Submodule.Quotient.mk 1)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hs1
  obtain ⟨r, hr⟩ := hs1
  change e11 * r = 1 * s at hr
  rw [one_mul] at hr
  have : e22 * s = 0 := by rw [← hr]; exact e22_mul_e11_mul r
  exact e22_ne_zero (hs.2 e22 this)

/-- The positive counterpart, checked by hand with `s = 1`: `I / e₁₁R` is
Goldie-torsion for `I = e₁₁R`. -/
theorem isGoldieTorsion_e11 : IsGoldieTorsion M2
    (↥(principalRightIdeal e11) ⧸ (principalRightIdeal e11).comap
      (principalRightIdeal e11).subtype) :=
  isGoldieTorsion_quotient_of_forall_exists_mul_mem fun y hy =>
    ⟨1, one_mem _, by rwa [mul_one]⟩

/-- Statement (a) at `M₂(ℚ)`. -/
example (I : Submodule M2ᵐᵒᵖ M2) :
    ∃ a ∈ I, ∀ y ∈ I, ∃ s ∈ M2⁰, y * s ∈ principalRightIdeal a :=
  exists_mem_forall_exists_mul_mem I

example : IsSimpleRing (QuotientRing M2) := inferInstance
example : IsSemisimpleRing (QuotientRing M2) := inferInstance
example : IsArtinianRing (QuotientRing M2) := inferInstance

example : ∃ (n : ℕ) (_ : NeZero n) (D : Type) (_ : DivisionRing D),
    Nonempty (QuotientRing M2 ≃+* Matrix (Fin n) (Fin n) D) :=
  exists_ringEquiv_matrix_divisionRing

/-- The zero divisor `e₁₁` survives in the quotient ring. -/
example : toQuotientRing M2 e11 ≠ 0 := fun h => by
  have := toQuotientRing_injective (h.trans (map_zero _).symm)
  have h11 := congrFun (congrFun this 0) 0
  simp [e11] at h11

/-! ## The field `ℚ`, with Mathlib's commutative Ore structure -/

instance : IsNoetherian ℚᵐᵒᵖ ℚ := isNoetherian_of_isNoetherianRing_op ℚ

/-- Hand computation, independent of Goldie's theorem: every nonzero element
`s⁻¹ r` of the quotient ring of `ℚ` is a unit, because `r ≠ 0` is itself a
denominator. Hence the quotient ring is a simple module over itself. -/
theorem isSimpleModule_rat :
    IsSimpleModule (OppositeQuotientRing ℚ) (OppositeQuotientRing ℚ) := by
  refine isSimpleModule_self_iff_isUnit.mpr ⟨?_, fun q hq => ?_⟩
  · exact OreLocalization.nontrivial_of_nonZeroDivisors fun x hx =>
      mem_oppositeSubmonoid_nonZeroDivisors.mp hx
  · induction q using OreLocalization.ind with
    | _ r s =>
      have hr : r ≠ 0 := by
        rintro rfl
        exact hq (OreLocalization.zero_oreDiv s)
      have hr' : r ∈ OreRightLocalization.oppositeSubmonoid ℚ⁰ :=
        mem_nonZeroDivisors_of_ne_zero (fun h => hr (unop_injective (h.trans unop_zero.symm)))
      let r' : OreRightLocalization.oppositeSubmonoid ℚ⁰ := ⟨r, hr'⟩
      refine isUnit_iff_exists.mpr ⟨(s : ℚᵐᵒᵖ) /ₒ r', ?_, ?_⟩
      · change ((r' : ℚᵐᵒᵖ) /ₒ s) * ((s : ℚᵐᵒᵖ) /ₒ r') = 1
        rw [OreLocalization.mul_cancel, OreLocalization.div_eq_one]
      · change ((s : ℚᵐᵒᵖ) /ₒ r') * ((r' : ℚᵐᵒᵖ) /ₒ s) = 1
        rw [OreLocalization.mul_cancel, OreLocalization.div_eq_one]

/-- The quotient ring of `ℚ` has length one; this agrees with the finiteness
and positivity proved for every simple right Noetherian ring. -/
theorem length_rat :
    Module.length (OppositeQuotientRing ℚ) (OppositeQuotientRing ℚ) = 1 :=
  have := isSimpleModule_rat
  Module.length_eq_one _ _

example : Module.length (OppositeQuotientRing ℚ) (OppositeQuotientRing ℚ) ≠ ⊤ :=
  length_oppositeQuotientRing_ne_top

end

end AlgebraicAnalysisTest.Goldie

#print axioms AlgebraicAnalysis.Goldie.exists_mem_nonZeroDivisors_of_isEssential
#print axioms AlgebraicAnalysis.Goldie.nonempty_oreSet_op
#print axioms AlgebraicAnalysis.Goldie.exists_mem_forall_exists_mul_mem
#print axioms AlgebraicAnalysis.Goldie.exists_mem_isGoldieTorsion_quotient
#print axioms AlgebraicAnalysis.Goldie.isSemisimpleRing_oppositeQuotientRing
#print axioms AlgebraicAnalysis.Goldie.isSimpleRing_oppositeQuotientRing
#print axioms AlgebraicAnalysis.Goldie.exists_ringEquiv_matrix_divisionRing
#print axioms AlgebraicAnalysis.Goldie.length_oppositeQuotientRing_ne_top
#print axioms AlgebraicAnalysis.Goldie.IsGoldieTorsion.exists_injective_right_mul
#print axioms AlgebraicAnalysis.Goldie.isGoldieTorsion_section
#print axioms AlgebraicAnalysisTest.Goldie.not_isGoldieTorsion_quotient_e11
#print axioms AlgebraicAnalysisTest.Goldie.length_rat
