import Mathlib

/-!
# Ring commutators

This module contains the multiplication identities used by both the Weyl
symplectic layer and the differential-Ore escape layer.  The convention is
`[u,v] = u*v - v*u`; no Weyl relation, Ore presentation, or application
specific structure is assumed.
-/

namespace AlgebraicAnalysis

section

variable {A : Type*} [Ring A]

/-- The ring commutator, with the written multiplication order retained. -/
def commutator (u v : A) : A := u * v - v * u

@[simp] theorem commutator_apply (u v : A) :
    commutator u v = u * v - v * u := rfl

/-- Leibniz expansion in the first argument. -/
theorem commutator_mul (u v x : A) :
    commutator (u * v) x =
      u * commutator v x + commutator u x * v := by
  simp only [commutator]
  noncomm_ring

/-- Iterated commutation with a Weyl-type relation. -/
theorem commutator_pow (z x : A) (h : commutator z x = 1) :
    ∀ n : ℕ, commutator (z ^ n) x = n • z ^ (n - 1)
  | 0 => by simp [commutator]
  | n + 1 => by
      rw [pow_succ, commutator_mul, h, commutator_pow z x h n]
      by_cases hn : n = 0
      · subst n
        simp
      · rw [smul_mul_assoc, Nat.succ_sub_one, mul_one, add_nsmul]
        have hpow : z ^ (n - 1) * z = z ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
        rw [hpow, one_nsmul]
        exact add_comm _ _

end

end AlgebraicAnalysis
