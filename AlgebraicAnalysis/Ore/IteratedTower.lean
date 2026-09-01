import AlgebraicAnalysis.Ore.Tower

/-!
# Finite iterated derivation-Ore towers

For a finite list of pairwise commuting coefficient derivations, this file
builds the corresponding iterated normal Ore ring.  The construction stores,
at every stage, the lift of every further commuting derivation and the proof
that such lifts commute.  Thus the construction can be iterated without any
new compatibility postulate.

The final result is an additive iterated normal-form equivalence.  Operator
faithfulness and freeness over a rational Weyl subring are deliberately not
asserted here.
-/

namespace AlgebraicAnalysis.OreIteratedTower

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreTower

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

variable {B : Type*} [Ring B]

abbrev Derivation (B : Type*) [Ring B] := OreDivisionDerivation B

/-- Commutation of two coefficient derivations. -/
def Commutes (D E : Derivation B) : Prop :=
  ∀ b : B, D (E b) = E (D b)

/-- Pairwise commutation for a finite ordered family. -/
def PairwiseCommutes : List (Derivation B) → Prop
  | [] => True
  | D :: Ds =>
      (∀ E ∈ Ds, Commutes D E) ∧ PairwiseCommutes Ds

/-- Commutation of one derivation with every member of a list. -/
def CommutesWith (D : Derivation B) : List (Derivation B) → Prop
  | Es => ∀ E ∈ Es, Commutes D E

lemma commutes_symm {D E : Derivation B} (h : Commutes D E) :
    Commutes E D := by
  intro b
  exact (h b).symm

lemma pairwise_tail {D : Derivation B} {Ds : List (Derivation B)}
    (h : PairwiseCommutes (D :: Ds)) : PairwiseCommutes Ds :=
  h.2

lemma pairwise_head {D : Derivation B} {Ds : List (Derivation B)}
    (h : PairwiseCommutes (D :: Ds)) : CommutesWith D Ds := by
  exact h.1

lemma commutesWith_tail {D E : Derivation B} {Es : List (Derivation B)}
    (h : CommutesWith D (E :: Es)) : CommutesWith D Es :=
  fun F hF => h F (by simp [hF])

lemma commutes_refl (D : Derivation B) : Commutes D D := by
  intro b
  rfl

/-! ## A recursive tower bundle -/

/--
`TowerBuild Ds h` contains the carrier ring for the tower on `Ds`, together
with the lift of any derivation commuting with `Ds`.  Bundling the lifts and
their commutation proof avoids a circular definition of the tower type.
-/
structure TowerBuild (Ds : List (Derivation B))
    (hDs : PairwiseCommutes Ds) where
  carrier : Type _
  ring : Ring carrier
  extend : ∀ (D : Derivation B), CommutesWith D Ds →
    OreDivisionDerivation carrier
  extend_commutes : ∀ (D E : Derivation B)
    (hD : CommutesWith D Ds) (hE : CommutesWith E Ds), Commutes D E →
    Commutes (extend D hD) (extend E hE)

def build : (Ds : List (Derivation B)) →
    (hDs : PairwiseCommutes Ds) → TowerBuild Ds hDs
  | [], _ =>
      { carrier := B
        ring := inferInstance
        extend := fun D _ => D
        extend_commutes := by
          intro D E _ _ hDE
          exact hDE }
  | E :: Es, hDs => by
      let T := build Es hDs.2
      letI : Ring T.carrier := T.ring
      let hE : CommutesWith E Es := pairwise_head hDs
      let DE : OreDivisionDerivation T.carrier := T.extend E hE
      refine
        { carrier := NormalOre DE
          ring := inferInstance
          extend := ?_
          extend_commutes := ?_ }
      · intro D hD
        exact liftDerivation DE (T.extend D (commutesWith_tail hD))
          (T.extend_commutes E D hE (commutesWith_tail hD)
            (commutes_symm (hD E (by simp))))
      · intro D F hD hF hDF
        exact liftDerivation_commute DE
          (T.extend D (commutesWith_tail hD))
          (T.extend F (commutesWith_tail hF))
          (T.extend_commutes E D hE (commutesWith_tail hD)
            (commutes_symm (hD E (by simp))))
          (T.extend_commutes E F hE (commutesWith_tail hF)
            (commutes_symm (hF E (by simp))))
          (T.extend_commutes D F (commutesWith_tail hD)
            (commutesWith_tail hF) hDF)

/-- The carrier ring of the finite iterated tower. -/
abbrev OreTower (Ds : List (Derivation B))
    (hDs : PairwiseCommutes Ds) : Type _ := (build Ds hDs).carrier

instance oreTowerRing (Ds : List (Derivation B))
    (hDs : PairwiseCommutes Ds) : Ring (OreTower Ds hDs) :=
  (build Ds hDs).ring

/-- The recursively lifted version of a coefficient derivation. -/
def extendThrough (D : Derivation B) (Ds : List (Derivation B))
    (hDs : PairwiseCommutes Ds) (hD : CommutesWith D Ds) :
    OreDivisionDerivation (OreTower Ds hDs) :=
  (build Ds hDs).extend D hD

theorem extendThrough_commutes (D E : Derivation B)
    (Ds : List (Derivation B)) (hDs : PairwiseCommutes Ds)
    (hD : CommutesWith D Ds) (hE : CommutesWith E Ds)
    (hDE : Commutes D E) :
    Commutes (extendThrough D Ds hDs hD)
      (extendThrough E Ds hDs hE) :=
  (build Ds hDs).extend_commutes D E hD hE hDE

/-! ## Iterated normal forms -/

/-- A nested polynomial carrier together with the ring instance it needs. -/
structure PolynomialBuild (Ds : List (Derivation B)) where
  carrier : Type _
  ring : Ring carrier

def polynomialBuild : (Ds : List (Derivation B)) → PolynomialBuild Ds
  | [] =>
      { carrier := B
        ring := inferInstance }
  | _ :: Ds => by
      let P := polynomialBuild Ds
      letI : Ring P.carrier := P.ring
      exact { carrier := Polynomial P.carrier
              ring := inferInstance }

/-- Nested coefficient-left polynomial data for the tower. -/
abbrev iteratedPolynomial (Ds : List (Derivation B)) : Type _ :=
  (polynomialBuild Ds).carrier

instance iteratedPolynomialRing (Ds : List (Derivation B)) :
    Ring (iteratedPolynomial Ds) :=
  (polynomialBuild Ds).ring

/-- Additive equivalence between nested polynomial data and the Ore tower. -/
def iteratedNormalForm : (Ds : List (Derivation B)) →
    (hDs : PairwiseCommutes Ds) →
    iteratedPolynomial Ds ≃+ OreTower Ds hDs
  | [], _ => AddEquiv.refl B
  | D :: Ds, hDs => by
      let T := build Ds hDs.2
      let P := polynomialBuild Ds
      letI : Ring P.carrier := P.ring
      let hD : CommutesWith D Ds := pairwise_head hDs
      let e : P.carrier ≃+ T.carrier :=
        iteratedNormalForm Ds hDs.2
      let ep : Polynomial P.carrier ≃+
          Polynomial T.carrier :=
        (Polynomial.toFinsuppIso P.carrier).toAddEquiv.trans
          ((Finsupp.mapRange.addEquiv e).trans
            (Polynomial.toFinsuppIso T.carrier).toAddEquiv.symm)
      exact ep.trans (normalFormAddEquiv (T.extend D hD))

theorem iteratedNormalForm_injective (Ds : List (Derivation B))
    (hDs : PairwiseCommutes Ds) :
    Function.Injective (iteratedNormalForm Ds hDs) :=
  (iteratedNormalForm Ds hDs).injective

theorem iteratedNormalForm_surjective (Ds : List (Derivation B))
    (hDs : PairwiseCommutes Ds) :
    Function.Surjective (iteratedNormalForm Ds hDs) :=
  (iteratedNormalForm Ds hDs).surjective

#print axioms build
#print axioms extendThrough_commutes
#print axioms iteratedNormalForm
#print axioms iteratedNormalForm_injective

end
end AlgebraicAnalysis.OreIteratedTower
