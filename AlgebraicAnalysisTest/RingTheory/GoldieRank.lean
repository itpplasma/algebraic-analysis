module

public import AlgebraicAnalysis.RingTheory.Goldie.Idempotents
public import AlgebraicAnalysisTest.RingTheory.Goldie

@[expose] public section

/-!
# Concrete oracles for Goldie rank and uniform dimension

* The field `ℚ`, with Mathlib's commutative Ore structure: the hand computation
  `length_rat` (every nonzero fraction is a unit) gives `goldieRank ℚ ℚ = 1`;
  the uniform dimension bridge then predicts that `ℚ` has no two independent
  nonzero submodules, which is checked directly (a nonzero submodule of a field
  is everything).
* The matrix ring `M₂(ℚ)`: the right ideals `e₁₁R` and `e₂₂R` are independent
  and nonzero (checked by matrix arithmetic), so the bridge gives
  `2 ≤ goldieRank M₂(ℚ) M₂(ℚ)`; the idempotent device then has at least two
  idempotents. The hostile control `R / e₁₁R` (not Goldie-torsion) has nonzero
  Goldie rank.
-/

namespace AlgebraicAnalysisTest.GoldieRank

noncomputable section

open AlgebraicAnalysis AlgebraicAnalysis.Goldie AlgebraicAnalysis.Module
  AlgebraicAnalysis.DenominatorTorsion AlgebraicAnalysisTest.Goldie
open MulOpposite nonZeroDivisors

/-! ## The field `ℚ` -/

/-- `s = rk(ℚ_ℚ) = 1`, from the hand computation of the length of the quotient
ring. -/
theorem goldieRank_rat : goldieRank ℚ ℚ = 1 :=
  (goldieRank_self ℚ).trans length_rat

example : goldieRank ℚ (Fin 3 → ℚᵐᵒᵖ) = 3 := by
  rw [goldieRank_pi_fin, goldieRank_op_self, length_rat, mul_one]
  rfl

/-- Bridge prediction: `ℚ` has uniform dimension at most one. -/
example : UniformDimLE ℚᵐᵒᵖ ℚ 1 :=
  uniformDimLE_self_iff.mpr goldieRank_rat.le

/-- Bridge prediction: `ℚ` has uniform dimension at least one. -/
example : UniformDimGE ℚᵐᵒᵖ ℚ 1 :=
  uniformDimGE_self_iff.mpr goldieRank_rat.ge

/-- Independent check of the bridge prediction: a nonzero submodule of the field
`ℚ` contains `1 = x x⁻¹`, so two nonzero submodules are never independent. -/
theorem not_uniformDimGE_rat_two : ¬ UniformDimGE ℚᵐᵒᵖ ℚ 2 := by
  rintro ⟨N, hN, hne⟩
  have htop : ∀ i, N i = ⊤ := by
    intro i
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
    rw [eq_top_iff]
    intro y _
    have : op (x⁻¹ * y) • x ∈ N i := (N i).smul_mem _ hx
    rwa [op_smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at this
  have h := (iSupIndep_pair (t := N) (i := 0) (j := 1) (by decide) (by decide)).mp hN
  rw [htop, htop, disjoint_self] at h
  exact hne 0 ((htop 0).trans h)

/-- The bridge and the hand computation agree. -/
example : ¬ UniformDimGE ℚᵐᵒᵖ ℚ 2 := by
  rw [uniformDimGE_self_iff, goldieRank_rat]
  decide

/-! ## The matrix ring `M₂(ℚ)` -/

theorem e11_mul_e11 : e11 * e11 = e11 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11, Matrix.mul_apply, Fin.sum_univ_two]

theorem e11_mul_e22 : e11 * e22 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11, e22, Matrix.mul_apply, Fin.sum_univ_two]

theorem e11_ne_zero : e11 ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [e11] at this

/-- The right ideals `e₁₁R` and `e₂₂R` of `M₂(ℚ)` are independent and nonzero:
if `e₁₁a = e₂₂b`, then `e₁₁a = e₁₁e₁₁a = e₁₁e₂₂b = 0`. -/
theorem uniformDimGE_M2_two : UniformDimGE M2ᵐᵒᵖ M2 2 := by
  refine ⟨![principalRightIdeal e11, principalRightIdeal e22], ?_, ?_⟩
  · rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (by decide)]
    rw [Submodule.disjoint_def]
    rintro x ⟨a, rfl⟩ ⟨b, hb⟩
    change e22 * b = e11 * a at hb
    change e11 * a = 0
    rw [← e11_mul_e11, mul_assoc, ← hb, ← mul_assoc, e11_mul_e22, zero_mul]
  · intro i
    fin_cases i
    · exact fun h => e11_ne_zero (by
        have : e11 * 1 ∈ principalRightIdeal e11 := ⟨1, rfl⟩
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at h
        rw [h, mul_one] at this
        exact (Submodule.mem_bot _).mp this)
    · exact fun h => e22_ne_zero (by
        have : e22 * 1 ∈ principalRightIdeal e22 := ⟨1, rfl⟩
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
        rw [h, mul_one] at this
        exact (Submodule.mem_bot _).mp this)

/-- Through the bridge: `rk(M₂(ℚ)) ≥ 2`. -/
theorem two_le_goldieRank_M2 : 2 ≤ goldieRank M2 M2 :=
  uniformDimGE_self_iff.mp uniformDimGE_M2_two

example : goldieRank M2 M2 ≠ ⊤ := goldieRank_self_ne_top

/-- The hostile control `R / e₁₁R`, which is not Goldie-torsion, has nonzero
Goldie rank. -/
example : goldieRank M2 (M2 ⧸ principalRightIdeal e11) ≠ 0 :=
  fun h => not_isGoldieTorsion_quotient_e11 (goldieRank_eq_zero_iff.mp h)

/-- The idempotent device for `M₂(ℚ)` has at least two idempotents. -/
example : ∃ (n : ℕ) (E : Fin n → QuotientRing M2), 2 ≤ n ∧ CompleteOrthogonalIdempotents E := by
  obtain ⟨n, E, -, -, -, -, hn, hE, -⟩ := exists_idempotent_denominators (R := M2)
  refine ⟨n, E, ?_, hE⟩
  have := two_le_goldieRank_M2.trans_eq hn.symm
  exact_mod_cast this

end

end AlgebraicAnalysisTest.GoldieRank

#print axioms AlgebraicAnalysis.OreModule.localizationMap_exact
#print axioms AlgebraicAnalysis.OreModule.uniformDimGE_iff_of_injective
#print axioms AlgebraicAnalysis.Module.uniformDimGE_iff_le_length
#print axioms AlgebraicAnalysis.Goldie.goldieRank_eq_add_of_exact
#print axioms AlgebraicAnalysis.Goldie.goldieRank_ne_top
#print axioms AlgebraicAnalysis.Goldie.uniformDimGE_quotient_iff
#print axioms AlgebraicAnalysis.Goldie.uniformDimLE_self_iff
#print axioms AlgebraicAnalysis.Goldie.le_mul_of_uniformDim
#print axioms AlgebraicAnalysis.Goldie.exists_idempotent_denominators
#print axioms AlgebraicAnalysisTest.GoldieRank.not_uniformDimGE_rat_two
#print axioms AlgebraicAnalysisTest.GoldieRank.two_le_goldieRank_M2
