module

public import AlgebraicAnalysis.LinearAlgebra.DivisionPencil

@[expose] public section

/-!
# Activated central pencils

A finite-dimensional domain and joint injectivity of `x ↦ (P x, T (Q x))`
make the pencil `P + κ(c) Q` generically injective when `T ∘ P = 0`.
The codomain need not be finite-dimensional, and the central field can have
arbitrary characteristic.

For a nonzero bad scalar, applying `T` puts its kernel vector in `ker (T ∘ Q)`.
On this fixed subspace `P` is injective, so the ordinary central-pencil theorem
applies. This avoids choosing a complement or rescaling a basis.
-/

namespace AlgebraicAnalysis

variable {k E D Z Z' : Type*} [Field k] [DivisionRing E]
variable [AddCommGroup D] [Module E D] [Module.Finite E D]
variable [AddCommGroup Z] [Module E Z] [AddCommGroup Z'] [Module E Z']

/-- An activated central pencil has a nonzero kernel at only finitely many
parameters. The activation map acts on the codomain: the hypothesis is
`T ∘ P = 0`. Joint injectivity is stated without choosing a product map. -/
theorem activated_pencil_ker_finite (κ : k →+* E)
    (hκ : ∀ (c : k) (a : E), κ c * a = a * κ c)
    (P Q : D →ₗ[E] Z) (T : Z →ₗ[E] Z') (hTP : T.comp P = 0)
    (hjoint : Function.Injective (fun x => (P x, T (Q x)))) :
    {c : k | ∃ d : D, d ≠ 0 ∧ P d + κ c • Q d = 0}.Finite := by
  classical
  let K := LinearMap.ker (T.comp Q)
  let PK : K →ₗ[E] Z := P.comp K.subtype
  let QK : K →ₗ[E] Z := Q.comp K.subtype
  have hPK : Function.Injective PK := by
    intro x y hxy
    apply Subtype.ext
    apply hjoint
    have hx : T (Q x) = 0 := x.property
    have hy : T (Q y) = 0 := y.property
    exact Prod.ext hxy (hx.trans hy.symm)
  refine ((pencil_ker_finite κ hκ PK QK hPK).union
    (Set.finite_singleton (0 : k))).subset ?_
  rintro c ⟨d, hd, hbad⟩
  by_cases hc : c = 0
  · exact Or.inr hc
  left
  have hTd : T (P d) = 0 := LinearMap.congr_fun hTP d
  have hTQ : T (Q d) = 0 := by
    have h := congrArg T hbad
    rw [map_add, map_smul, hTd, zero_add, map_zero] at h
    exact (smul_eq_zero.mp h).resolve_left (by simpa only [map_zero] using κ.injective.ne hc)
  refine ⟨⟨d, hTQ⟩, ?_, hbad⟩
  intro h
  exact hd (congrArg Subtype.val h)

/-- Under activation and joint injectivity, `P + κ(c) Q` is injective for all
but finitely many central field parameters, without a characteristic restriction. -/
theorem activated_pencil_finite (κ : k →+* E)
    (hκ : ∀ (c : k) (a : E), κ c * a = a * κ c)
    (P Q : D →ₗ[E] Z) (T : Z →ₗ[E] Z') (hTP : T.comp P = 0)
    (hjoint : Function.Injective (fun x => (P x, T (Q x)))) :
    {c : k | ¬ Function.Injective (fun d => P d + κ c • Q d)}.Finite := by
  refine (activated_pencil_ker_finite κ hκ P Q T hTP hjoint).subset ?_
  intro c hc
  by_contra hnone
  apply hc
  intro x y hxy
  by_contra hne
  apply hnone
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  change P x + κ c • Q x = P y + κ c • Q y at hxy
  rw [map_sub, map_sub, smul_sub, sub_add_sub_comm, hxy, sub_self]

end AlgebraicAnalysis
