module
public import AlgebraicAnalysis.Module.Deviation
public import Mathlib.Algebra.Algebra.Bilinear

@[expose] public section

/-!
# Deviation at omega and quotients by injective endomorphisms

`Module.DevLEOmega` asks for eventually finite-deviation successive intervals,
without a uniform finite bound on these intervals. The descending ranges of
an injective endomorphism have isomorphic successive intervals. Consequently
its cokernel has finite deviation under this omega bound, and loses one
stratum under a finite bound. Left multiplication on a right regular module
specializes this to `R/dR` in a domain. No Noetherian or Ore hypothesis is
needed for these conclusions.
-/

universe u v

namespace Module

/-- Deviation at most omega, expressed without assigning an ordinal dimension. -/
def DevLEOmega (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ c : ℕ → Submodule R M, Antitone c → ∃ N, ∀ i, N ≤ i →
    ∃ n, Order.DevLE n (Set.Icc (c (i + 1)) (c i))

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

theorem DevLE.omega {n : ℕ} (h : DevLE R n M) : DevLEOmega R M :=
  fun _c _ => ⟨0, fun _i _ => ⟨n, Order.DevLE.interval h _ _⟩⟩

/-- Each successive range interval of an injective endomorphism is the
submodule lattice of its cokernel. -/
noncomputable def quotientRangePowOrderIso (f : M →ₗ[R] M) (hf : Function.Injective f)
    (i : ℕ) : Submodule R (M ⧸ LinearMap.range f) ≃o
      Set.Icc (LinearMap.range (f ^ (i + 1))) (LinearMap.range (f ^ i)) := by
  have hfi : Function.Injective (f ^ i) := Module.End.iterate_injective hf i
  have he : LinearMap.range (f ^ (i + 1)) = (LinearMap.range f).map (f ^ i) := by
    rw [Module.End.iterate_succ, LinearMap.range_comp]
  refine
    { toFun := fun U => ⟨(U.comap (LinearMap.range f).mkQ).map (f ^ i),
        ?_, ?_⟩
      invFun := fun U => (U.val.comap (f ^ i)).map (LinearMap.range f).mkQ
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · rw [he]
    exact Submodule.map_mono (Submodule.le_comap_mkQ _ _)
  · rintro x ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  · intro U
    dsimp
    rw [Submodule.comap_map_eq_of_injective hfi]
    exact Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _) U
  · intro U
    apply Subtype.ext
    dsimp
    have hl : LinearMap.range f ≤ U.val.comap (f ^ i) := by
      rw [← Submodule.map_le_iff_le_comap, ← he]
      exact U.property.1
    rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hl,
      Submodule.map_comap_eq, inf_eq_right.mpr U.property.2]
  · intro U V
    change (U.comap _).map (f ^ i) ≤ (V.comap _).map (f ^ i) ↔ U ≤ V
    rw [Submodule.map_le_map_iff_of_injective hfi,
      Submodule.comap_le_comap_iff_of_surjective (Submodule.mkQ_surjective _)]

/-- An injective endomorphism lowers a positive finite deviation bound on its cokernel. -/
theorem DevLE.quotient_range_of_injective {n : ℕ} (h : DevLE R (n + 1) M)
    (f : M →ₗ[R] M) (hf : Function.Injective f) : DevLE R n (M ⧸ LinearMap.range f) := by
  obtain ⟨N, hN⟩ := h f.iterateRange f.iterateRange.monotone
  exact (Order.devLE_orderIso_iff n (quotientRangePowOrderIso f hf N)).mpr
    (hN N le_rfl)

/-- The omega bound gives a finite bound on the cokernel of an injective endomorphism. -/
theorem DevLEOmega.quotient_range_of_injective (h : DevLEOmega R M)
    (f : M →ₗ[R] M) (hf : Function.Injective f) :
    ∃ n, DevLE R n (M ⧸ LinearMap.range f) := by
  obtain ⟨N, hN⟩ := h f.iterateRange f.iterateRange.monotone
  obtain ⟨n, hn⟩ := hN N le_rfl
  exact ⟨n, (Order.devLE_orderIso_iff n (quotientRangePowOrderIso f hf N)).mpr hn⟩

/-- The strict-stratum version includes the Artinian-to-zero endpoint. -/
theorem Small.quotient_range_of_injective {e : ℕ} (h : Small R (e + 1) M)
    (f : M →ₗ[R] M) (hf : Function.Injective f) : Small R e (M ⧸ LinearMap.range f) := by
  cases e with
  | zero =>
    have : IsArtinian R M := devLE_zero_iff_isArtinian.mp h
    have hs : Function.Surjective f := IsArtinian.surjective_of_injective_endomorphism f hf
    exact Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr hs)
  | succ e => exact DevLE.quotient_range_of_injective h f hf

section Domain

variable {D : Type u} [Ring D] [IsDomain D]

/-- The successive intervals of `R ⊇ dR ⊇ d²R ⊇ …`, with the right-sided
convention explicit, are all the submodule lattice of `R/dR`. -/
noncomputable def principalRightPowOrderIso {d : D} (hd : d ≠ 0) (i : ℕ) :
    Submodule Dᵐᵒᵖ (D ⧸ LinearMap.range (LinearMap.mulLeft Dᵐᵒᵖ d)) ≃o
      Set.Icc (LinearMap.range (LinearMap.mulLeft Dᵐᵒᵖ (d ^ (i + 1))))
        (LinearMap.range (LinearMap.mulLeft Dᵐᵒᵖ (d ^ i))) := by
  rw [← LinearMap.pow_mulLeft Dᵐᵒᵖ D d (i + 1),
    ← LinearMap.pow_mulLeft Dᵐᵒᵖ D d i]
  exact quotientRangePowOrderIso (LinearMap.mulLeft Dᵐᵒᵖ d)
    (fun _ _ hxy => mul_left_cancel₀ hd hxy) i

/-- In a domain, the right principal quotient drops a finite deviation stratum. -/
theorem Small.principal_right_quotient {e : ℕ} (h : Small Dᵐᵒᵖ (e + 1) D)
    {d : D} (hd : d ≠ 0) :
    Small Dᵐᵒᵖ e (D ⧸ LinearMap.range (LinearMap.mulLeft Dᵐᵒᵖ d)) :=
  h.quotient_range_of_injective (LinearMap.mulLeft Dᵐᵒᵖ d)
    (fun _ _ hxy => mul_left_cancel₀ hd hxy)

/-- Under the omega deviation bound, every nonzero principal right quotient
has finite deviation. Units are allowed and yield the zero quotient. -/
theorem DevLEOmega.principal_right_quotient (h : DevLEOmega Dᵐᵒᵖ D)
    {d : D} (hd : d ≠ 0) :
    ∃ n, DevLE Dᵐᵒᵖ n (D ⧸ LinearMap.range (LinearMap.mulLeft Dᵐᵒᵖ d)) :=
  h.quotient_range_of_injective (LinearMap.mulLeft Dᵐᵒᵖ d)
    (fun _ _ hxy => mul_left_cancel₀ hd hxy)

end Domain

end Module
