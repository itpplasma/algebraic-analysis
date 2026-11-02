module
public import Mathlib.Algebra.RingQuot
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.LinearAlgebra.SymplecticGroup
public import AlgebraicAnalysis.Commutator

@[expose] public section

/-!
# Presentation of the Weyl algebra

The Weyl algebra `A_n(k)` of `n` degrees of freedom is the free algebra on
`2n` generators `x_1, …, x_n, ∂_1, …, ∂_n` modulo the commutator relations
`[x_i, ∂_j] = -δ_ij` (the standard symplectic form `Matrix.J`), so that
`[∂_i, x_j] = δ_ij`.  This file records only the presentation and the ordered
PBW words used by the Weyl applications.

Provenance: the definitions `freeWeylRelation`, `FreeWeyl`, `freeWeylGenerator`,
`PhaseVar`, `relation`, `WeylAlg`, `generator`, `oldIndex`, `freeOldMap`,
`freeOrderedMonomial`, `orderedMonomial` and `phaseDegree` are copied from
`Stafford38/ChallengeDefinitions.lean` of `itpplasma/stafford38-formal` at
commit `ac20b730fb368786e840320ebf6e62d19bbe29f3` (Apache-2.0).  The bodies are
unchanged; only the namespace moved from `Stafford` and `Stafford38Challenge`
to `AlgebraicAnalysis.Weyl`.  Consequently `AlgebraicAnalysis.Weyl.WeylAlg k n`
is, definitionally, the algebra `Stafford38Challenge.WeylAlg k n` of
stafford38-formal.  The challenge-level `bernsteinPiece`, `bernsteinDegree`
and fixed-source statements are not part of this extraction.
-/

namespace AlgebraicAnalysis.Weyl

variable {k ι : Type*} [Field k]

/-- The commutator relations presenting a Weyl-type algebra: `[a, b] = ω i j`
for the generators `a = ι i`, `b = ι j` written in the free algebra. -/
def freeWeylRelation (omega : Matrix ι ι k)
    (a b : FreeAlgebra k ι) : Prop :=
  ∃ i j,
    a = FreeAlgebra.ι k i * FreeAlgebra.ι k j -
      FreeAlgebra.ι k j * FreeAlgebra.ι k i ∧
    b = algebraMap k (FreeAlgebra k ι) (omega i j)

/-- The free algebra modulo the commutator relations encoded by `omega`. -/
abbrev FreeWeyl (k : Type*) [Field k] (ι : Type*)
    (omega : Matrix ι ι k) := RingQuot (freeWeylRelation omega)

/-- The canonical generator of the presented Weyl-type algebra. -/
def freeWeylGenerator (omega : Matrix ι ι k) (i : ι) : FreeWeyl k ι omega :=
  RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k i)

/-- Index type of the coordinate `x_i` (left summand) and momentum `∂_i`
(right summand) generators. -/
abbrev PhaseVar (n : ℕ) := Fin n ⊕ Fin n

/-- The Weyl commutator relation for the standard symplectic matrix. -/
abbrev relation {n : ℕ}
    (omega : Matrix (PhaseVar n) (PhaseVar n) k)
    (a b : FreeAlgebra k (PhaseVar n)) : Prop :=
  freeWeylRelation omega a b

/-- The standard presented Weyl algebra `A_n(k)`. -/
abbrev WeylAlg (k : Type*) [Field k] (n : ℕ) :=
  FreeWeyl k (PhaseVar n) (Matrix.J (Fin n) k)

/-- A named generator of the presented Weyl algebra. -/
abbrev generator (k : Type*) [Field k] (n : ℕ) (i : PhaseVar n) : WeylAlg k n :=
  freeWeylGenerator (Matrix.J (Fin n) k) i

/-- Insert an old phase variable after the newest coordinate or momentum. -/
def oldIndex {n : ℕ} : PhaseVar n → PhaseVar (n + 1)
  | .inl i => .inl i.succ
  | .inr i => .inr i.succ

@[simp] theorem oldIndex_inl {n : ℕ} (i : Fin n) :
    oldIndex (.inl i) = .inl i.succ := rfl

@[simp] theorem oldIndex_inr {n : ℕ} (i : Fin n) :
    oldIndex (.inr i) = .inr i.succ := rfl

/-- Insert an old free-algebra word into the next-rank free algebra. -/
def freeOldMap (k : Type*) [Field k] (n : ℕ) :
    FreeAlgebra k (PhaseVar n) →ₐ[k] FreeAlgebra k (PhaseVar (n + 1)) :=
  FreeAlgebra.lift k (fun i => FreeAlgebra.ι k (oldIndex i))

/-- Ordered PBW words, with old pairs followed by the newest pair. -/
def freeOrderedMonomial (k : Type*) [Field k] :
    (n : ℕ) → (Fin n → ℕ) → (Fin n → ℕ) → FreeAlgebra k (PhaseVar n)
  | 0, _, _ => 1
  | n + 1, a, p =>
      freeOldMap k n
          (freeOrderedMonomial k n (fun i => a i.succ) (fun i => p i.succ)) *
        FreeAlgebra.ι k (.inl (0 : Fin (n + 1))) ^ a 0 *
        FreeAlgebra.ι k (.inr (0 : Fin (n + 1))) ^ p 0

/-- The image of an ordered PBW word in the presented Weyl algebra. -/
def orderedMonomial (k : Type*) [Field k] (n : ℕ)
    (a p : Fin n → ℕ) : WeylAlg k n :=
  RingQuot.mkAlgHom k (relation (k := k) (n := n) (Matrix.J (Fin n) k))
    (freeOrderedMonomial k n a p)

/-- Total degree of a split coordinate/momentum exponent. -/
def phaseDegree {n : ℕ} (a p : Fin n → ℕ) : ℕ :=
  (∑ i, a i) + ∑ i, p i

/-- The canonical generators satisfy the defining relations: the commutator of
`freeWeylGenerator omega i` and `freeWeylGenerator omega j` is `omega i j`. -/
theorem freeWeylGenerator_commutator
    (omega : Matrix ι ι k) (i j : ι) :
    ringCommutator (freeWeylGenerator omega i) (freeWeylGenerator omega j) =
      algebraMap k (FreeWeyl k ι omega) (omega i j) := by
  have h := RingQuot.mkAlgHom_rel k
    (show freeWeylRelation omega
      (FreeAlgebra.ι k i * FreeAlgebra.ι k j -
        FreeAlgebra.ι k j * FreeAlgebra.ι k i)
      (algebraMap k (FreeAlgebra k ι) (omega i j)) from ⟨i, j, rfl, rfl⟩)
  simp only [freeWeylGenerator, ringCommutator, RingQuot.mkAlgHom_coe]
  calc
    RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k i) *
          RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k j) -
        RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k j) *
          RingQuot.mkAlgHom k (freeWeylRelation omega) (FreeAlgebra.ι k i) =
      RingQuot.mkAlgHom k (freeWeylRelation omega)
        (FreeAlgebra.ι k i * FreeAlgebra.ι k j -
          FreeAlgebra.ι k j * FreeAlgebra.ι k i) := by
            rw [← map_mul, ← map_mul, ← map_sub]
    _ = RingQuot.mkAlgHom k (freeWeylRelation omega)
        ((algebraMap k (FreeAlgebra k ι)) (omega i j)) := h
    _ = algebraMap k (FreeWeyl k ι omega) (omega i j) := by
      have hmap : algebraMap k (FreeWeyl k ι omega) =
          (RingQuot.mkAlgHom k (freeWeylRelation omega)).toRingHom.comp
            (algebraMap k (FreeAlgebra k ι)) := by
        apply RingHom.ext
        intro c
        change algebraMap k (FreeWeyl k ι omega) c =
          RingQuot.mkAlgHom k (freeWeylRelation omega)
            (algebraMap k (FreeAlgebra k ι) c)
        exact (RingQuot.mkAlgHom k (freeWeylRelation omega)).commutes c |>.symm
      rw [hmap]
      rfl

end AlgebraicAnalysis.Weyl
