import Mathlib.RingTheory.Finiteness.Projective

/-!
# Stable freeness interface for projective modules

This module records the application-independent right-module formulation of
stable freeness used in filtered-ring arguments.  It is a definition, not a
claim that any particular ring has the property.


## References and proof context

[HTT08] Ryoshi Hotta, Kiyoshi Takeuchi, and Toshiyuki Tanisaki, *D-Modules, Perverse Sheaves, and Representation Theory*, Progress in Mathematics 236, Birkhäuser, 2008.
https://doi.org/10.1007/978-0-8176-4523-6

General filtered D-module context only: this file defines an interface and does not prove a stable-freeness theorem. See docs/literature.md and docs/extraction-review-literature-interfaces.md.
-/

namespace AlgebraicAnalysis
namespace StablyFree

universe u

/-- Every finitely generated projective right `R`-module becomes finite free
after adding a finite free summand.  Right modules are represented as modules
over `Rᵐᵒᵖ`, so the order of scalar multiplication remains explicit. -/
def StablyFreeProjectives (R : Type u) [Ring R] : Prop :=
  ∀ (P : Type u) [AddCommGroup P] [Module Rᵐᵒᵖ P],
    Module.Projective Rᵐᵒᵖ P → Module.Finite Rᵐᵒᵖ P →
      ∃ m n : ℕ,
        Nonempty (P × (Fin m → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ))

end StablyFree
end AlgebraicAnalysis
