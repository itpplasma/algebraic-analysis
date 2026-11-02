module
public import AlgebraicAnalysis.Enveloping.PBWFiltration
public import AlgebraicAnalysis.Filtration.SymbolPresentation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial

@[expose] public section

/-!
# Surjective symbol presentation of the PBW filtration

Let `b : Basis (Fin m) k L` be a basis of the Lie algebra `L` and let
`G = MvPolynomial (Fin m) k`, graded by total degree. A monomial `X^α` is sent to the
ordered product `b₀^{α₀} ⋯ b_{m-1}^{α_{m-1}}` in `R`, extended linearly. This gives
`ψ : G → R`, and its graded pieces `σₙ : Gₙ → Fₙ/Fₙ₋₁` form a surjective symbol
presentation of the PBW filtration `pbwFiltration π hπ` (`pbwSymbolPresentation`).

The argument uses only the reordering lemma of `PBWFiltration`:

* Multiplicativity. For homogeneous `g` of degree `i` and `h` of degree `j`,
  `ψ(g h) - ψ(g) ψ(h)` lies in `F_{i+j-1}`. Expanding over monomials reduces this to
  the rearrangement of the letters of `X^α X^β`.
* Surjectivity. Let `Eₙ = ψ(𝒜ₙ) + Fₙ₋₁`. Left multiplication by a basis generator sends
  `Eₙ` into `Eₙ₊₁`, by the multiplicativity above with `X_j`. Induction on words then gives
  `Fₙ ⊆ Eₙ`, that is, every class of `Fₙ/Fₙ₋₁` is the image of a degree-`n` polynomial.

No injectivity of `σₙ` is claimed. The presentation gives right and left Noetherianity of
`R` and deviation at most `dim L` on both sides, by `RingFiltration.SymbolPresentation`
and `ringKrullDim k[X₀, …, X_{m-1}] = m`.

## Main results

* `pbwSymbolPresentation`: the surjective symbol presentation of `pbwFiltration π hπ`.
* `isNoetherian_right_of_surjective`, `isNoetherianRing_of_surjective`,
  `devLE_right_of_surjective`, `devLE_left_of_surjective`: for `L` finite-dimensional and a
  surjective algebra map `π : U(L) → R`, `R` is Noetherian on both sides, and
  `Module.DevLE` holds with bound `dim L` on both sides.
-/

namespace AlgebraicAnalysis.Enveloping

open MvPolynomial DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

section Letters

variable {k : Type*} [Field k] {L : Type*} [LieRing L] [LieAlgebra k L]
variable {m : ℕ} (b : Module.Basis (Fin m) k L)

/-- The ordered word `b₀^{α₀} ⋯ b_{m-1}^{α_{m-1}}` of basis letters of multidegree `α`. -/
def letters (α : Fin m →₀ ℕ) : List L :=
  (List.finRange m).flatMap fun i => List.replicate (α i) (b i)

theorem letters_zero : letters b 0 = [] := by
  simp [letters]

theorem length_letters (α : Fin m →₀ ℕ) : (letters b α).length = ∑ i, α i := by
  simp [letters, List.length_flatMap, List.length_replicate, Fin.sum_univ_def]

/-- The length of `letters b α` is the total degree of `α`. -/
theorem length_letters_eq_weight (α : Fin m →₀ ℕ) :
    (letters b α).length = Finsupp.weight (fun _ : Fin m => (1 : ℕ)) α := by
  rw [length_letters, Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp
  · simp

open scoped Classical in
/-- Multiplicities of a letter in `letters b α`. -/
theorem count_letters (α : Fin m →₀ ℕ) (x : L) :
    (letters b α).count x = ∑ i, if b i = x then α i else 0 := by
  simp only [letters, List.count_flatMap, Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  by_cases h : b i = x <;> simp [List.count_replicate, h]

open scoped Classical in
/-- The letters of `α + β` are a rearrangement of the letters of `α` followed by those of `β`. -/
theorem letters_add_perm (α β : Fin m →₀ ℕ) :
    (letters b (α + β)).Perm (letters b α ++ letters b β) := by
  rw [List.perm_iff_count]
  intro x
  rw [List.count_append, count_letters, count_letters, count_letters]
  simp only [Finsupp.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

open scoped Classical in
/-- A single basis letter `b j` is the length-one word of `X j`, up to rearrangement. -/
theorem letters_single_perm (j : Fin m) : (letters b (Finsupp.single j 1)).Perm [b j] := by
  rw [List.perm_iff_count]
  intro x
  rw [count_letters]
  simp only [List.count_singleton]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp only [Finsupp.single_apply, Ne.symm hij, ite_false, ite_self]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Letters

section Symbol

variable {k : Type*} [Field k] {L : Type*} [LieRing L] [LieAlgebra k L]
variable {R : Type*} [Ring R] [Algebra k R]
variable {m : ℕ} (b : Module.Basis (Fin m) k L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The coefficient map of a polynomial, as a `k`-linear map to finitely supported functions. -/
def coeffLinear : MvPolynomial (Fin m) k →ₗ[k] ((Fin m →₀ ℕ) →₀ k) where
  toFun p := p.coeff
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The symbol `ψ : MvPolynomial (Fin m) k → R`: a monomial `X^α` goes to the ordered
product of the basis letters of multidegree `α`, extended `k`-linearly. -/
noncomputable def psi (π : UniversalEnvelopingAlgebra k L →ₐ[k] R) :
    MvPolynomial (Fin m) k →ₗ[k] R :=
  (Finsupp.linearCombination k (fun α : Fin m →₀ ℕ => wordProd π (letters b α))).comp
    coeffLinear

variable (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)

theorem psi_monomial (α : Fin m →₀ ℕ) (c : k) :
    psi b π (monomial α c) = c • wordProd π (letters b α) := by
  show Finsupp.linearCombination k (fun α : Fin m →₀ ℕ => wordProd π (letters b α))
    (Finsupp.single α c) = _
  rw [Finsupp.linearCombination_single]

theorem psi_one : psi b π 1 = 1 := by
  rw [show (1 : MvPolynomial (Fin m) k) = monomial 0 1 from rfl, psi_monomial, letters_zero,
    one_smul, wordProd_nil]

theorem psi_X (j : Fin m) : psi b π (X j) = wordProd π (letters b (Finsupp.single j 1)) := by
  rw [X, psi_monomial, one_smul]

theorem psi_eq_sum (g : MvPolynomial (Fin m) k) :
    psi b π g = ∑ α ∈ g.support, g.coeff α • wordProd π (letters b α) := by
  rw [psi, LinearMap.comp_apply, Finsupp.linearCombination_apply]
  rfl

/-- Degree-`n` polynomials have symbols in `Fₙ`. -/
theorem psi_mem_pbwPiece {n : ℕ} {g : MvPolynomial (Fin m) k}
    (hg : g ∈ homogeneousSubmodule (Fin m) k n) : psi b π g ∈ pbwPiece π n := by
  rw [psi_eq_sum]
  refine Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ ?_
  refine wordProd_mem_pbwPiece π (le_of_eq ?_)
  rw [length_letters_eq_weight]
  exact (mem_homogeneousSubmodule n g).mp hg (mem_support_iff.mp hα)

/-- Permuting a word changes its product by an element of the filtration piece of its length. -/
theorem wordProd_sub_mem_below (hπ : Function.Surjective π) {w w' : List L} (h : w.Perm w') :
    wordProd π w - wordProd π w' ∈ (pbwFiltration π hπ).below w.length := by
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · have h1 : w = [] := List.length_eq_zero_iff.mp h0
    have h2 : w' = [] := List.length_eq_zero_iff.mp (by rw [← h.length_eq, h1]; rfl)
    subst h1 h2
    simp
  · obtain ⟨n, hn⟩ : ∃ n, w.length = n + 1 := ⟨w.length - 1, by omega⟩
    rw [hn, RingFiltration.below_succ, pbwFiltration_F]
    exact wordProd_sub_mem_pbwPiece π h n hn.le

/-- Monomial multiplicativity: `ψ(X^{α+β}) ≡ ψ(X^α) ψ(X^β)` modulo lower filtration. -/
theorem wordProd_mul_sub_mem_below (hπ : Function.Surjective π) (α β : Fin m →₀ ℕ) :
    wordProd π (letters b (α + β)) - wordProd π (letters b α) * wordProd π (letters b β) ∈
      (pbwFiltration π hπ).below (letters b (α + β)).length := by
  rw [← wordProd_append]
  exact wordProd_sub_mem_below π hπ (letters_add_perm b α β)

/-- **Multiplicativity of the symbol.** For homogeneous `g` of degree `i` and `h` of degree `j`,
`ψ(g h) ≡ ψ(g) ψ(h)` modulo `F_{i+j-1}`. Expanding both sides over the monomials of `g` and `h`
reduces this to the monomial case. -/
theorem psi_mul_sub_mem_below (hπ : Function.Surjective π) {g h : MvPolynomial (Fin m) k}
    {i j : ℕ} (hg : g ∈ homogeneousSubmodule (Fin m) k i)
    (hh : h ∈ homogeneousSubmodule (Fin m) k j) :
    psi b π (g * h) - psi b π g * psi b π h ∈ (pbwFiltration π hπ).below (i + j) := by
  have hmul : psi b π (g * h) = ∑ α ∈ g.support, ∑ β ∈ h.support,
      (g.coeff α * h.coeff β) • wordProd π (letters b (α + β)) := by
    rw [MvPolynomial.mul_def]
    simp only [Finsupp.sum, map_sum, psi_monomial]
    rfl
  have key : psi b π (g * h) - psi b π g * psi b π h =
      ∑ α ∈ g.support, ∑ β ∈ h.support,
        (g.coeff α * h.coeff β) •
          (wordProd π (letters b (α + β)) - wordProd π (letters b α) * wordProd π (letters b β)) := by
    rw [hmul, psi_eq_sum b π g, psi_eq_sum b π h, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [smul_mul_smul_comm, smul_sub]
  rw [key]
  refine Submodule.sum_mem _ fun α hα => Submodule.sum_mem _ fun β hβ => Submodule.smul_mem _ _ ?_
  have hα' : (letters b α).length = i := by
    rw [length_letters_eq_weight]
    exact (mem_homogeneousSubmodule i g).mp hg (mem_support_iff.mp hα)
  have hβ' : (letters b β).length = j := by
    rw [length_letters_eq_weight]
    exact (mem_homogeneousSubmodule j h).mp hh (mem_support_iff.mp hβ)
  have hdeg : (letters b (α + β)).length = i + j := by
    rw [(letters_add_perm b α β).length_eq, List.length_append, hα', hβ']
  have := wordProd_mul_sub_mem_below b π hπ α β
  rwa [hdeg] at this

/-- The subspace `Eₙ = ψ(𝒜ₙ) + Fₙ₋₁` of `R`. Its image in `Fₙ/Fₙ₋₁` is all of it. -/
def E (hπ : Function.Surjective π) (n : ℕ) : Submodule k R :=
  Submodule.map (psi b π) (homogeneousSubmodule (Fin m) k n) ⊔ (pbwFiltration π hπ).below n

variable {π} (hπ : Function.Surjective π)

theorem E_le_pbwPiece (n : ℕ) : E b π hπ n ≤ pbwPiece π n := by
  refine sup_le ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact psi_mem_pbwPiece b π hg
  · cases n with
    | zero => simp
    | succ n => exact (le_of_eq (RingFiltration.below_succ _ n)).trans (pbwPiece_mono π (Nat.le_succ n))

theorem pbwPiece_le_E_succ (n : ℕ) : pbwPiece π n ≤ E b π hπ (n + 1) := by
  refine le_trans (le_of_eq ?_) le_sup_right
  exact (RingFiltration.below_succ (pbwFiltration π hπ) n).symm

theorem E_le_succ (n : ℕ) : E b π hπ n ≤ E b π hπ (n + 1) :=
  (E_le_pbwPiece b hπ n).trans (pbwPiece_le_E_succ b hπ n)

theorem E_mono {a c : ℕ} (h : a ≤ c) : E b π hπ a ≤ E b π hπ c :=
  (monotone_nat_of_le_succ (E_le_succ b hπ)) h

theorem one_mem_homogeneous_zero : (1 : MvPolynomial (Fin m) k) ∈
    homogeneousSubmodule (Fin m) k 0 :=
  (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_one (Fin m) k)

/-- The expansion of a Lie element in the chosen basis. -/
theorem gen_eq_sum (x : L) : gen π x = ∑ j, b.repr x j • gen π (b j) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [gen, map_sum, map_smul]

/-- Left multiplication by a basis generator sends `E_n` into `E_{n+1}`. Here `ψ(X_j g)` is
the degree-`n+1` term and `ψ(X_j) ψ(g) ≡ gen(b_j) ψ(g)`, both modulo lower filtration. -/
theorem gen_basis_mul_E (j : Fin m) {n : ℕ} {e : R} (he : e ∈ E b π hπ n) :
    gen π (b j) * e ∈ E b π hπ (n + 1) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp he
  rw [mul_add]
  refine Submodule.add_mem _ ?_ ?_
  · obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
    have hX : (X j : MvPolynomial (Fin m) k) ∈ homogeneousSubmodule (Fin m) k 1 :=
      (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X k j)
    have hXg : X j * g ∈ homogeneousSubmodule (Fin m) k (n + 1) := by
      rw [mem_homogeneousSubmodule, add_comm]
      exact (isHomogeneous_X k j).mul ((mem_homogeneousSubmodule n g).mp hg)
    have hA := psi_mul_sub_mem_below b π hπ hX hg
    rw [add_comm 1 n] at hA
    have hB : psi b π (X j) - gen π (b j) ∈ (pbwFiltration π hπ).below 1 := by
      have h1 := wordProd_sub_mem_below π hπ (letters_single_perm b j)
      rw [(letters_single_perm b j).length_eq, List.length_singleton] at h1
      rw [psi_X, ← wordProd_singleton π (b j)]
      exact h1
    have hBg : (psi b π (X j) - gen π (b j)) * psi b π g ∈ pbwPiece π n := by
      have h := mul_mem_pbwPiece π hB (psi_mem_pbwPiece b π hg)
      simpa only [Nat.zero_add] using h
    have key : gen π (b j) * psi b π g =
        psi b π (X j * g) - (psi b π (X j * g) - psi b π (X j) * psi b π g) -
          (psi b π (X j) - gen π (b j)) * psi b π g := by
      noncomm_ring
    rw [key]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hXg)
    · exact Submodule.mem_sup_right hA
    · exact Submodule.mem_sup_right hBg
  · have h := (pbwFiltration π hπ).mul_below_le 1 n
      (Submodule.mul_mem_mul (gen_mem_pbwPiece_one π (b j)) hz)
    rw [add_comm 1 n] at h
    exact Submodule.mem_sup_right h

theorem gen_mul_E (x : L) {n : ℕ} {e : R} (he : e ∈ E b π hπ n) :
    gen π x * e ∈ E b π hπ (n + 1) := by
  rw [gen_eq_sum b x, Finset.sum_mul]
  exact Submodule.sum_mem _ fun j _ => by
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (gen_basis_mul_E b hπ j he)

/-- Every ordered product of Lie elements lies in `E` at its length. -/
theorem wordProd_mem_E (w : List L) : wordProd π w ∈ E b π hπ w.length := by
  induction w with
  | nil =>
    rw [wordProd_nil, List.length_nil]
    exact Submodule.mem_sup_left (Submodule.mem_map.mpr ⟨1, one_mem_homogeneous_zero, psi_one b π⟩)
  | cons x w ih =>
    rw [wordProd_cons, List.length_cons]
    exact gen_mul_E b hπ x ih

theorem pbwPiece_le_E (n : ℕ) : pbwPiece π n ≤ E b π hπ n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, hw, rfl⟩
  exact E_mono b hπ hw (wordProd_mem_E b hπ w)

/-- The graded symbol `σₙ : 𝒜ₙ → Fₙ/Fₙ₋₁` induced by `ψ`. -/
noncomputable def sym (n : ℕ) :
    homogeneousSubmodule (Fin m) k n →ₗ[k] (pbwFiltration π hπ).GradedQuotient n :=
  ((pbwFiltration π hπ).belowInF n).mkQ ∘ₗ
    LinearMap.codRestrict ((pbwFiltration π hπ).F n)
      ((psi b π).comp (homogeneousSubmodule (Fin m) k n).subtype)
      (fun g => psi_mem_pbwPiece b π g.2)

theorem sym_apply (n : ℕ) (g : homogeneousSubmodule (Fin m) k n) :
    sym b hπ n g = Submodule.Quotient.mk ⟨psi b π g, psi_mem_pbwPiece b π g.2⟩ :=
  rfl

theorem sym_surjective (n : ℕ) : Function.Surjective (sym b hπ n) := by
  intro q
  obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (pbwPiece_le_E b hπ n hu)
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [sym_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [(pbwFiltration π hπ).mem_belowInF]
  show psi b π g - u ∈ _
  have hd : psi b π g - u = -z := by rw [← hyz]; abel
  rw [hd]
  exact Submodule.neg_mem _ hz

theorem sym_mul (i j : ℕ) (g : homogeneousSubmodule (Fin m) k i)
    (h : homogeneousSubmodule (Fin m) k j) (x : homogeneousSubmodule (Fin m) k (i + j))
    (hx : (x : MvPolynomial (Fin m) k) = g * h) :
    sym b hπ (i + j) x = (pbwFiltration π hπ).gradedMul i j (sym b hπ i g) (sym b hπ j h) := by
  rw [sym_apply, sym_apply, sym_apply, RingFiltration.gradedMul_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [(pbwFiltration π hπ).mem_belowInF]
  show psi b π x - psi b π g * psi b π h ∈ _
  rw [hx]
  exact psi_mul_sub_mem_below b π hπ g.2 h.2

/-- **Surjective symbol presentation of the PBW filtration** by the polynomial ring
`MvPolynomial (Fin m) k`, graded by total degree. -/
noncomputable def pbwSymbolPresentation :
    (pbwFiltration π hπ).SymbolPresentation (homogeneousSubmodule (Fin m) k) where
  sym := sym b hπ
  sym_surjective := sym_surjective b hπ
  sym_mul := sym_mul b hπ

end Symbol

end

section Results

variable {k : Type*} [Field k] {L : Type*} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
variable {R : Type*} [Ring R] [Algebra k R]

/-- The Krull dimension of a polynomial ring in `m` variables over a field is `m`. -/
theorem ringKrullDim_mvPolynomial_fin (m : ℕ) :
    ringKrullDim (MvPolynomial (Fin m) k) = m := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field k]
  simp

variable (π : UniversalEnvelopingAlgebra k L →ₐ[k] R)

/-- **Right Noetherianity of a quotient of `U(L)`.** For `L` finite-dimensional and `π` a
surjective algebra map `U(L) → R`, the ring `R` is right Noetherian. -/
theorem isNoetherian_right_of_surjective (hπ : Function.Surjective π) :
    IsNoetherian Rᵐᵒᵖ R :=
  (pbwSymbolPresentation (Module.finBasis k L) hπ).isNoetherian_right

/-- **Left Noetherianity of a quotient of `U(L)`.** -/
theorem isNoetherianRing_of_surjective (hπ : Function.Surjective π) :
    IsNoetherianRing R :=
  (pbwSymbolPresentation (Module.finBasis k L) hπ).isNoetherianRing

/-- **Right deviation.** With `m = dim L`, the right ideals of `R` have deviation at most `m`. -/
theorem devLE_right_of_surjective (hπ : Function.Surjective π) :
    Module.DevLE Rᵐᵒᵖ (Module.finrank k L) R :=
  (pbwSymbolPresentation (Module.finBasis k L) hπ).devLE_right (Module.finrank k L)
    (ringKrullDim_mvPolynomial_fin _).le

/-- **Left deviation.** With `m = dim L`, the left ideals of `R` have deviation at most `m`. -/
theorem devLE_left_of_surjective (hπ : Function.Surjective π) :
    Module.DevLE R (Module.finrank k L) R :=
  (pbwSymbolPresentation (Module.finBasis k L) hπ).devLE_left (Module.finrank k L)
    (ringKrullDim_mvPolynomial_fin _).le

end Results

end AlgebraicAnalysis.Enveloping
