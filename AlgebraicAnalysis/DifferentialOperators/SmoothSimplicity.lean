module
public import AlgebraicAnalysis.DifferentialOperators.CoordinateSimplicity
public import AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialOperators
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

/-!
# Smooth domains have no differential ideals; `D_k(A)` is simple

Let `k` be a field of characteristic zero and `A` a smooth `k`-algebra which is
a domain. Then the only nonzero ideal of `A` stable under all `k`-derivations is
`A` itself (`eq_top_of_derivation_mem_of_smooth`), and therefore `D_k(A)` is a
simple ring (`isSimpleRing_of_smooth`, by `isSimpleRing_of_derivation`).

## Proof

* **Polynomial rings** (`eq_top_of_forall_pderiv_mem`): partial derivatives
  lower the total degree of a nonzero element of a differential ideal until a
  nonzero constant is reached.
* **Quasi-finite algebras over a polynomial ring with dual derivations**
  (`eq_top_of_derivation_mem_of_quasiFinite`). Let `R` be a domain and a
  quasi-finite `k[X_σ]`-algebra with derivations `∂ᵢ`, `∂ᵢ(Xⱼ) = δᵢⱼ`. Then
  `∂ᵢ(p) = ∂p/∂Xᵢ` on polynomials, so the kernel of `k[X] → R` is a
  differential ideal, hence zero. If `J ⊆ R` is a nonzero `∂`-stable ideal
  meeting no nonzero polynomial, a prime `Q ⊇ J` avoiding them lies over the
  zero ideal, as does the prime `0 ⊊ Q`, contradicting incomparability of
  primes in quasi-finite fibres. So `J` contains a nonzero polynomial `c`, and
  `{p | p ∈ J}` is a nonzero differential ideal of `k[X]`, hence contains `1`.
* **Standard smooth algebras** (`eq_top_of_derivation_mem_of_isStandardSmooth`).
  `Ω_{R/k}` has a basis `d s₁, …, d s_d` (Mathlib's
  `IsStandardSmooth.iff_exists_basis_kaehlerDifferential`). Making `R` a
  `k[X₁, …, X_d]`-algebra by `Xᵢ ↦ sᵢ`, the relative differentials vanish, so
  `R` is unramified, hence quasi-finite, over `k[X]`; the dual basis gives the
  derivations `∂ᵢ`.
* **Smooth algebras** (`eq_top_of_derivation_mem_of_smooth`). `Spec A` is
  covered by standard opens `D(g)` with `A_g` standard smooth
  (`Algebra.Smooth.exists_span_eq_top_isStandardSmooth`). A derivation of
  `A_g` restricted to `A` becomes, after multiplication by a power of `g`, a
  derivation of `A` (`exists_derivation_eq_pow_smul`), so `J A_g` is a
  differential ideal of `A_g`, hence `A_g`, and some power of `g` lies in `J`.
  If `J ⊆ 𝔪` maximal, choose `g ∉ 𝔪`.

The route through quasi-finiteness and the local structure of smooth algebras
is AA-native. For the statement compare [McConnell–Robson, *Noncommutative
Noetherian Rings*, 15.3.8] and [Coutinho, *A Primer of Algebraic D-modules*,
Theorem 3.2.4 for polynomial rings].
-/

namespace AlgebraicAnalysis.DifferentialOperators

open MvPolynomial

section Polynomial

variable {k σ : Type*} [Field k] [CharZero k]

/-- **Polynomial rings have no differential ideals** in characteristic zero:
the only nonzero ideal of `k[X_σ]` stable under all `∂/∂Xᵢ` is `k[X_σ]`. -/
theorem eq_top_of_forall_pderiv_mem (J : Ideal (MvPolynomial σ k)) (hJ : J ≠ ⊥)
    (hD : ∀ i, ∀ p ∈ J, pderiv i p ∈ J) : J = ⊤ := by
  have key : ∀ d, ∀ p : MvPolynomial σ k, p.totalDegree ≤ d → p ≠ 0 → p ∈ J → J = ⊤ := by
    intro d
    induction d with
    | zero =>
        intro p hp hp0 hpJ
        obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨_, totalDegree_eq_zero_iff_eq_C.mp (by omega)⟩
        have hc : c ≠ 0 := fun h => hp0 (by rw [h, C_0])
        exact Ideal.eq_top_of_isUnit_mem J hpJ ((IsUnit.mk0 c hc).map C)
    | succ d ih =>
        intro p hp hp0 hpJ
        by_cases hall : ∀ i, pderiv i p = 0
        · rw [LocalizedPolynomialOperators.eq_C_of_pderiv_eq_zero hall] at hpJ hp0
          exact ih _ (by simp) hp0 hpJ
        · push Not at hall
          obtain ⟨i, hi⟩ := hall
          exact ih _ ((LocalizedPolynomialOperators.totalDegree_pderiv_le p i).trans (by omega)) hi
            (hD i _ hpJ)
  obtain ⟨p, hpJ, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  exact key _ p le_rfl hp0 hpJ

end Polynomial

section QuasiFinite

variable {k R σ : Type*} [Field k] [CommRing R] [Algebra k R]
  [Algebra (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R] [DecidableEq σ]
  {D : σ → Derivation k R R}

omit [DecidableEq σ] in
/-- Derivations dual to the coordinates act on polynomials as partial
derivatives: `∂ᵢ(p) = ∂p/∂Xᵢ`. -/
theorem derivation_algebraMap_eq_pderiv [DecidableEq σ]
    (hdual : ∀ i j, D i (algebraMap (MvPolynomial σ k) R (X j)) = if i = j then 1 else 0)
    (i : σ) (p : MvPolynomial σ k) :
    D i (algebraMap _ R p) = algebraMap _ R (pderiv i p) := by
  have h : (D i).compAlgebraMap (MvPolynomial σ k) =
      (Algebra.linearMap (MvPolynomial σ k) R).compDer (pderiv i) := by
    refine MvPolynomial.derivation_ext fun j => ?_
    rw [Derivation.compAlgebraMap_apply, hdual]
    change _ = algebraMap (MvPolynomial σ k) R (pderiv i (X j))
    rw [pderiv_X]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Pi.single_apply, Ne.symm hij]
  exact Derivation.congr_fun h p

variable [CharZero k] [IsDomain R] [Algebra.QuasiFinite (MvPolynomial σ k) R]

/-- **Quasi-finite algebras over a polynomial ring have no differential
ideals.** Let `R` be a domain and a quasi-finite `k[X_σ]`-algebra with
derivations `∂ᵢ` dual to the `Xᵢ`. Then the only nonzero ideal of `R` stable
under all `∂ᵢ` is `R`. -/
theorem eq_top_of_derivation_mem_of_quasiFinite
    (hdual : ∀ i j, D i (algebraMap (MvPolynomial σ k) R (X j)) = if i = j then 1 else 0)
    (J : Ideal R) (hJ : J ≠ ⊥) (hD : ∀ i, ∀ f ∈ J, D i f ∈ J) : J = ⊤ := by
  have hpd := derivation_algebraMap_eq_pderiv hdual
  -- the pull-back of a differential ideal is differential
  have hcomap : ∀ I : Ideal R, (∀ i, ∀ f ∈ I, D i f ∈ I) →
      ∀ i, ∀ p ∈ I.comap (algebraMap (MvPolynomial σ k) R), pderiv i p ∈
        I.comap (algebraMap (MvPolynomial σ k) R) := fun I hI i p hp => by
    rw [Ideal.mem_comap, ← hpd]
    exact hI i _ hp
  -- the coordinates are algebraically independent
  have hker : (⊥ : Ideal R).comap (algebraMap (MvPolynomial σ k) R) = ⊥ := by
    by_contra h
    have htop := eq_top_of_forall_pderiv_mem _ h (hcomap ⊥ fun i f hf => by
      rw [Ideal.mem_bot] at hf ⊢
      rw [hf, map_zero])
    have h1 : (1 : MvPolynomial σ k) ∈ (⊥ : Ideal R).comap (algebraMap (MvPolynomial σ k) R) :=
      htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one, Ideal.mem_bot] at h1
    exact one_ne_zero h1
  -- `J` contains the image of a nonzero polynomial
  obtain ⟨c, hc0, hcJ⟩ : ∃ c : MvPolynomial σ k, c ≠ 0 ∧ algebraMap _ R c ∈ J := by
    by_contra hcon
    push Not at hcon
    let M := Algebra.algebraMapSubmonoid R (nonZeroDivisors (MvPolynomial σ k))
    obtain ⟨Q, hQ, hJQ, hQM⟩ := Ideal.exists_le_prime_disjoint J M (by
      rw [Set.disjoint_left]
      rintro _ hJ' ⟨c, hc, rfl⟩
      exact hcon c (nonZeroDivisors.ne_zero hc) hJ')
    have hunder : (⊥ : Ideal R).under (MvPolynomial σ k) = Q.under (MvPolynomial σ k) := by
      rw [Ideal.under_def, Ideal.under_def, hker, eq_comm, eq_bot_iff]
      intro p hp
      rw [Ideal.mem_bot]
      by_contra hp0
      exact Set.disjoint_left.mp hQM hp ⟨p, mem_nonZeroDivisors_of_ne_zero hp0, rfl⟩
    have hQ0 := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := MvPolynomial σ k) ⊥ Q bot_le
      hunder
    exact hJ (eq_bot_iff.mpr (hQ0 ▸ hJQ))
  -- the polynomials in `J` form a nonzero differential ideal
  have htop := eq_top_of_forall_pderiv_mem _ (fun h => hc0 (by
      have : c ∈ J.comap (algebraMap (MvPolynomial σ k) R) := hcJ
      rwa [h, Ideal.mem_bot] at this)) (hcomap J hD)
  have h1 : (1 : MvPolynomial σ k) ∈ J.comap (algebraMap (MvPolynomial σ k) R) :=
    htop ▸ Submodule.mem_top
  rw [Ideal.mem_comap, map_one] at h1
  exact Ideal.eq_top_of_isUnit_mem J h1 isUnit_one

end QuasiFinite

section StandardSmooth

variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]

/-- **Standard smooth domains have no differential ideals** in characteristic
zero. -/
theorem eq_top_of_derivation_mem_of_isStandardSmooth [Algebra.IsStandardSmooth k R]
    (J : Ideal R) (hJ : J ≠ ⊥) (hD : ∀ D : Derivation k R R, ∀ f ∈ J, D f ∈ J) : J = ⊤ := by
  classical
  obtain ⟨-, I, b, hb⟩ :=
    (Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential (R := k) (S := R)).mp
      inferInstance
  have : Finite I := Module.Finite.finite_basis b
  have : Fintype I := Fintype.ofFinite I
  choose s hs using fun i => hb ⟨i, rfl⟩
  let : Algebra (MvPolynomial I k) R := (MvPolynomial.aeval s).toAlgebra
  have halg : ∀ p, algebraMap (MvPolynomial I k) R p = MvPolynomial.aeval s p := fun _ => rfl
  have : IsScalarTower k (MvPolynomial I k) R := IsScalarTower.of_algebraMap_eq fun c => by
    rw [halg, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  -- the relative differentials vanish
  have : Subsingleton (Ω[R⁄MvPolynomial I k]) := by
    have hzero : KaehlerDifferential.map k (MvPolynomial I k) R R = 0 := by
      refine b.ext fun i => ?_
      rw [← hs i, KaehlerDifferential.map_D, LinearMap.zero_apply, Algebra.algebraMap_self,
        RingHom.id_apply, show s i = algebraMap (MvPolynomial I k) R (X i) by
          rw [halg, MvPolynomial.aeval_X], Derivation.map_algebraMap]
    refine ⟨fun ω ω' => ?_⟩
    obtain ⟨η, rfl⟩ := KaehlerDifferential.map_surjective k (MvPolynomial I k) R ω
    obtain ⟨η', rfl⟩ := KaehlerDifferential.map_surjective k (MvPolynomial I k) R ω'
    rw [hzero, LinearMap.zero_apply, LinearMap.zero_apply]
  have : Algebra.FormallyUnramified (MvPolynomial I k) R := ⟨inferInstance⟩
  have : Algebra.FiniteType (MvPolynomial I k) R :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial I k) R
  have : Algebra.QuasiFinite (MvPolynomial I k) R := inferInstance
  -- the dual derivations
  let D : I → Derivation k R R := fun i => (b.coord i).compDer (KaehlerDifferential.D k R)
  refine eq_top_of_derivation_mem_of_quasiFinite (D := D) (fun i j => ?_) J hJ
    fun i => hD (D i)
  rw [halg, MvPolynomial.aeval_X]
  change b.coord i (KaehlerDifferential.D k R (s j)) = _
  rw [hs, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]

end StandardSmooth

section Localization

variable {k A R : Type*} [CommRing k] [CommRing A] [CommRing R] [Algebra k A] [Algebra k R]
  [Algebra A R] [IsScalarTower k A R]

/-- **Clearing denominators of a derivation.** Let `R = A[g⁻¹]` with `A → R`
injective and `Ω_{A/k}` finitely generated. For every `k`-derivation
`δ : A → R` there are `N` and a derivation `E` of `A` with `E = g^N δ`. -/
theorem exists_derivation_eq_pow_smul (g : A) [IsLocalization.Away g R]
    (hinj : Function.Injective (algebraMap A R)) [Module.Finite A (Ω[A⁄k])]
    (δ : Derivation k A R) :
    ∃ N : ℕ, ∃ E : Derivation k A A, ∀ a, algebraMap A R (E a) = g ^ N • δ a := by
  classical
  set ψ := δ.liftKaehlerDifferential
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := Ω[A⁄k])
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers g) (S.image ψ)
  have hint : ∀ ω, IsLocalization.IsInteger A ((g ^ N : A) • ψ ω) := by
    intro ω
    have hω : ω ∈ Submodule.span A (S : Set (Ω[A⁄k])) := hS ▸ Submodule.mem_top
    induction hω using Submodule.span_induction with
    | mem ω hω => exact hN _ (Finset.mem_image_of_mem ψ hω)
    | zero => rw [map_zero, smul_zero]; exact ⟨0, map_zero _⟩
    | add ω ω' _ _ h h' => rw [map_add, smul_add]; exact IsLocalization.isInteger_add h h'
    | smul a ω _ h => rw [map_smul, smul_comm]; exact IsLocalization.isInteger_smul h
  let T : Submodule A R := LinearMap.range (Algebra.linearMap A R)
  let ψ₁ : Ω[A⁄k] →ₗ[A] T := ((g ^ N : A) • ψ).codRestrict T fun ω => by
    obtain ⟨a, ha⟩ := hint ω
    exact ⟨a, ha⟩
  let e : A ≃ₗ[A] T := LinearEquiv.ofInjective (Algebra.linearMap A R) hinj
  refine ⟨N, (e.symm.toLinearMap ∘ₗ ψ₁).compDer (KaehlerDifferential.D k A), fun a => ?_⟩
  have key : ∀ y : T, algebraMap A R (e.symm y) = y := fun y => by
    conv_rhs => rw [← e.apply_symm_apply y]
    rfl
  change algebraMap A R (e.symm (ψ₁ (KaehlerDifferential.D k A a))) = _
  rw [key]
  simp [ψ₁, ψ]

end Localization

section Smooth

variable {k A : Type*} [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.Smooth k A]

/-- **Smooth domains have no differential ideals** in characteristic zero: the
only nonzero ideal of `A` stable under all `k`-derivations is `A`. -/
theorem eq_top_of_derivation_mem_of_smooth (J : Ideal A) (hJ : J ≠ ⊥)
    (hD : ∀ D : Derivation k A A, ∀ f ∈ J, D f ∈ J) : J = ⊤ := by
  obtain ⟨s, hs, hstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth k A
  by_contra hJtop
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJtop
  obtain ⟨g, hgs, hgm⟩ : ∃ g ∈ s, g ∉ m := by
    by_contra h
    push Not at h
    exact hm.ne_top (eq_top_iff.mpr (hs ▸ Ideal.span_le.mpr h))
  have hg0 : g ≠ 0 := fun h => hgm (h ▸ m.zero_mem)
  let R := Localization.Away g
  have hle : Submonoid.powers g ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg0
  have : IsDomain R := IsLocalization.isDomain_of_le_nonZeroDivisors R hle
  have hinj : Function.Injective (algebraMap A R) := IsLocalization.injective R hle
  have := hstd g hgs
  -- the extension of `J` is a differential ideal of `A_g`
  let J' : Ideal R := J.map (algebraMap A R)
  have hJ' : J' ≠ ⊥ := by
    obtain ⟨j, hjJ, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    intro h
    have : algebraMap A R j ∈ J' := Ideal.mem_map_of_mem _ hjJ
    rw [h, Ideal.mem_bot] at this
    exact hj0 (hinj (this.trans (map_zero _).symm))
  have hD' : ∀ D : Derivation k R R, ∀ f ∈ J', D f ∈ J' := by
    intro D f hf
    have hgen : ∀ j ∈ J, D (algebraMap A R j) ∈ J' := by
      intro j hj
      obtain ⟨N, E, hE⟩ := exists_derivation_eq_pow_smul g hinj (D.compAlgebraMap A)
      have h1 : algebraMap A R (E j) ∈ J' := Ideal.mem_map_of_mem _ (hD E j hj)
      rw [hE, Derivation.compAlgebraMap_apply, Algebra.smul_def] at h1
      have hu : IsUnit (algebraMap A R (g ^ N)) :=
        IsLocalization.map_units R (⟨g ^ N, N, rfl⟩ : Submonoid.powers g)
      obtain ⟨u, hu⟩ := hu
      have := J'.mul_mem_left (↑u⁻¹ : R) h1
      rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨j, hj, rfl⟩ := hf
        exact hgen j hj
    | zero => rw [map_zero]; exact J'.zero_mem
    | add f f' _ _ h h' => rw [map_add]; exact J'.add_mem h h'
    | smul r f hf h =>
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact J'.add_mem (J'.mul_mem_left r h) (J'.mul_mem_right _ hf)
  have htop := eq_top_of_derivation_mem_of_isStandardSmooth (k := k) J' hJ' hD'
  -- a power of `g` lies in `J ⊆ 𝔪`
  have h1 : (1 : R) ∈ J' := htop ▸ Submodule.mem_top
  obtain ⟨⟨⟨j, hj⟩, ⟨_, n, rfl⟩⟩, hjn⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g) R).mp h1
  simp only [one_mul] at hjn
  have hgn : g ^ n = j := hinj hjn
  exact hgm (hm.isPrime.mem_of_pow_mem n (hgn ▸ hJm hj))

/-- **`D_k(A)` is simple** for a smooth domain `A` over a field of
characteristic zero. -/
theorem isSimpleRing_of_smooth : IsSimpleRing (algebra (k := k) (R := A)) :=
  isSimpleRing_of_derivation eq_top_of_derivation_mem_of_smooth

end Smooth

end AlgebraicAnalysis.DifferentialOperators
