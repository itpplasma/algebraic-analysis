module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.Length

@[expose] public section

/-!
# Embedding the regular module over a simple Artinian ring

Over a simple Artinian ring `A` every module is a direct sum of copies of the
unique simple module (Wedderburn–Artin). Hence a finitely generated module `X`
with `length A ≤ length X` contains a copy of the regular module `A`, that is,
an element with zero annihilator.

## Main results

* `AlgebraicAnalysis.exists_injective_smul_of_length_le`: if
  `Module.length A A ≤ Module.length A X`, some `x : X` makes `a ↦ a • x`
  injective.

## References

T. Y. Lam, *A First Course in Noncommutative Rings*, §3 (semisimple modules
and isotypic components). Nothing here is new.
-/

namespace AlgebraicAnalysis

universe u v

/-- **Embedding the regular module.** Over a simple Artinian ring `A`, a finitely
generated module `X` with `length A ≤ length X` contains an element `x` with zero
annihilator, i.e. `a ↦ a • x` is injective. Both modules are direct sums of copies
of the unique simple module (Wedderburn–Artin), so `A` embeds in `X`. -/
theorem exists_injective_smul_of_length_le {A : Type u} [Ring A] [IsSimpleRing A]
    [IsArtinianRing A] {X : Type v} [AddCommGroup X] [Module A X] [Module.Finite A X]
    (h : Module.length A A ≤ Module.length A X) :
    ∃ x : X, Function.Injective fun a : A => a • x := by
  classical
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A A)
  have : IsSimpleModule A S := isSimpleModule_iff_isAtom.mpr hS
  have hAS : IsIsotypicOfType A A S := IsSimpleRing.isIsotypic A A S
  have hXS : IsIsotypicOfType A X S := by
    intro T _
    have hP := IsSimpleRing.isIsotypic A (A × X)
    have e1 := Submodule.equivMapOfInjective (LinearMap.inl A A X) LinearMap.inl_injective S
    have e2 := Submodule.equivMapOfInjective (LinearMap.inr A A X) LinearMap.inr_injective T
    have : IsSimpleModule A (S.map (LinearMap.inl A A X)) := IsSimpleModule.congr e1.symm
    have : IsSimpleModule A (T.map (LinearMap.inr A A X)) := IsSimpleModule.congr e2.symm
    obtain ⟨e⟩ := hP (S.map (LinearMap.inl A A X)) (T.map (LinearMap.inr A A X))
    exact ⟨e2.trans (e.trans e1.symm)⟩
  obtain ⟨a, ⟨ea⟩⟩ := hAS.linearEquiv_fun
  obtain ⟨b, ⟨eb⟩⟩ := hXS.linearEquiv_fun
  have hab : a ≤ b := by
    have h1 := ea.length_eq
    have h2 := eb.length_eq
    simp only [Module.length_pi, ENat.card_eq_coe_fintype_card, Fintype.card_fin,
      Module.length_eq_one, mul_one] at h1 h2
    rw [h1, h2] at h
    exact_mod_cast h
  let ι : (Fin a → S) →ₗ[A] (Fin b → S) :=
    LinearMap.pi fun j => if hj : (j : ℕ) < a then LinearMap.proj ⟨j, hj⟩ else 0
  have hι : Function.Injective ι := by
    intro g g' hgg
    funext i
    have := congrFun hgg (Fin.castLE hab i)
    simpa [ι, i.2] using this
  let φ : A →ₗ[A] X := eb.symm.toLinearMap ∘ₗ ι ∘ₗ ea.toLinearMap
  have hφ : Function.Injective φ := eb.symm.injective.comp (hι.comp ea.injective)
  refine ⟨φ 1, fun c c' hcc => hφ ?_⟩
  simpa [← map_smul] using hcc

end AlgebraicAnalysis
