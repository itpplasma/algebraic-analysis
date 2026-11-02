module

public import AlgebraicAnalysis.Filtration.GradedSymbol

@[expose] public section

/-!
# Filtered rings whose associated graded ring is a domain

Let `φ` be an ascending, exhaustive, submultiplicative filtration of the
`R`-algebra `A`, and let `S : φ.GradedSymbol 𝒜` identify `gr A` with a
commutative graded algebra `G = ⨁ 𝒜 n`. If `G` has no zero divisors, then
neither has `A`; if moreover `G` is nontrivial and `1 ∈ 𝒜 0`, then `A` is a
domain (the standard argument for filtered rings, cf.
[McConnell–Robson, *Noncommutative Noetherian Rings*, §1.6]).

## Proof

A nonzero `a ∈ A` has an order `i = φ.order a`, the least `i` with
`a ∈ F i`. Its symbol in degree `i` is nonzero, since the kernel of the
degree-`i` symbol is `F (i - 1)` (`grAt_order_ne_zero`). For nonzero `a`, `b`
of orders `i`, `j` the symbol of `a b` in degree `i + j` is the product of
the two nonzero symbols, which is nonzero in `G`, so `a b ≠ 0`.
-/

namespace AlgebraicAnalysis

namespace RingFiltration

namespace GradedSymbol

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing G] [Algebra R G]
variable {φ : RingFiltration R A} {𝒜 : ℕ → Submodule R G} (S : GradedSymbol φ 𝒜)

/-- The symbol of a nonzero element in the degree of its order is nonzero. -/
theorem grAt_order_ne_zero {a : A} (ha : a ≠ 0) : S.grAt (φ.order ha) a ≠ 0 := by
  rw [Ne, S.grAt_eq_zero_iff (φ.mem_order ha)]
  intro h
  rcases hi : φ.order ha with _ | i
  · rw [hi, below_zero, Submodule.mem_bot] at h
    exact ha h
  · rw [hi, below_succ] at h
    have := φ.order_le ha h
    omega

include S in
/-- **A filtered ring whose associated graded ring has no zero divisors has
no zero divisors.** -/
theorem noZeroDivisors [NoZeroDivisors G] : NoZeroDivisors A where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    by_contra h
    push Not at h
    obtain ⟨ha, hb⟩ := h
    have hmul := S.grAt_mul (φ.mem_order ha) (φ.mem_order hb)
    have h0 : S.grAt (φ.order ha + φ.order hb) (0 : A) = 0 := by
      rw [S.grAt_of_mem (zero_mem _)]
      exact congrArg Subtype.val (map_zero (S.gr _))
    rw [hab, h0] at hmul
    exact mul_ne_zero (S.grAt_order_ne_zero ha) (S.grAt_order_ne_zero hb) hmul.symm

include S in
/-- A filtered ring is nontrivial when its associated graded ring is
nontrivial with `1` of degree `0`: an element of `F 0` with symbol `1` is
nonzero. -/
theorem nontrivial [Nontrivial G] (h1 : (1 : G) ∈ 𝒜 0) : Nontrivial A := by
  obtain ⟨u, hu, hsymb⟩ := S.exists_grAt_eq h1
  refine ⟨⟨u, 0, fun hu0 => one_ne_zero (α := G) ?_⟩⟩
  rw [← hsymb, S.grAt_eq_zero_iff hu, below_zero, Submodule.mem_bot]
  exact hu0

include S in
/-- **A filtered ring whose associated graded ring is a domain, with `1` of
degree `0`, is a domain.** -/
theorem isDomain [IsDomain G] (h1 : (1 : G) ∈ 𝒜 0) : IsDomain A :=
  haveI := S.noZeroDivisors
  haveI := S.nontrivial h1
  NoZeroDivisors.to_isDomain A

end GradedSymbol

end RingFiltration

end AlgebraicAnalysis
