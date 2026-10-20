import SymmetricSubgroupAsymptotics.PrimitiveAffinePublishedSmallStructuralInput
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeDegreeSource

/-!
# Structure preceding the degree-five affine classification

The regular normal subgroup and its faithful conjugation action already
force the orders `5`, `10`, and `20`. This module proves that reduction for
the original action, and constructs the cyclic model in the order-five
branch. The dihedral identification and the literal natural-action
identification at order twenty are separate remaining obligations; this
module does not assert an inhabitant of the published classification.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

variable {L : Type} [Group L] [Finite L] [MulAction L (Fin 5)]
  [FaithfulSMul L (Fin 5)] (P : PrimitiveAffineProfile L (Fin 5))

omit [FaithfulSMul L (Fin 5)] in
/-- At degree five the regular translation subgroup has order five. -/
theorem degreeFive_translation_card (x : Fin 5) : Nat.card P.V = 5 := by
  simpa only [Nat.card_fin] using P.card_eq x

/-- The faithful point stabilizer embeds into the four-element automorphism
group of the cyclic translation subgroup. No primitive classification is
used here. -/
theorem degreeFive_complement_card_dvd_four (x : Fin 5) :
    Nat.card (P.complement x) ∣ 4 := by
  letI : IsCyclic P.V :=
    P.translation_isCyclic_of_degree_prime x (by norm_num)
  have hdiv := Subgroup.card_dvd_of_injective (P.complementAction x)
    (P.complementAction_injective x)
  have hAut : Nat.card (MulAut P.V) = 4 := by
    rw [IsCyclic.card_mulAut, P.degreeFive_translation_card x,
      Nat.totient_prime (by norm_num : Nat.Prime 5)]
  simpa only [hAut] using hdiv

/-- These are the complete possible orders of the actual point stabilizer. -/
theorem degreeFive_complement_card_cases (x : Fin 5) :
    Nat.card (P.complement x) = 1 ∨
      Nat.card (P.complement x) = 2 ∨
      Nat.card (P.complement x) = 4 := by
  have hdiv := P.degreeFive_complement_card_dvd_four x
  have hle : Nat.card (P.complement x) ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
  have hpos : 0 < Nat.card (P.complement x) := Nat.card_pos
  have hcases : Nat.card (P.complement x) = 1 ∨
      Nat.card (P.complement x) = 2 ∨
      Nat.card (P.complement x) = 3 ∨
      Nat.card (P.complement x) = 4 := by omega
  rcases hcases with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rw [h] at hdiv
    norm_num at hdiv
  · exact Or.inr (Or.inr h)

include P in
/-- The order-five, order-ten, and order-twenty alternatives are forced by
regularity and faithfulness alone. -/
theorem degreeFive_card_cases (x : Fin 5) :
    Nat.card L = 5 ∨ Nat.card L = 10 ∨ Nat.card L = 20 := by
  have hfactor := (P.isComplement'_complement x).card_mul
  rw [P.degreeFive_translation_card x] at hfactor
  rcases P.degreeFive_complement_card_cases x with h | h | h
  · left
    simpa only [h, mul_one] using hfactor.symm
  · right; left
    simpa only [h] using hfactor.symm
  · right; right
    simpa only [h] using hfactor.symm

/-- The cyclic degree-five model can be constructed solely from the ambient
order; it carries no new group-theoretic premise. -/
def degreeFive_cyclicEquiv_of_card_eq_five
    (hcard : Nat.card L = 5) : L ≃* Multiplicative (ZMod 5) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply mulEquivOfPrimeCardEq (p := 5) hcard
  change Nat.card (ZMod 5) = 5
  exact Nat.card_zmod 5

/-- A trivial stabilizer gives the cyclic branch explicitly. -/
def degreeFive_cyclicEquiv_of_complement_card_eq_one
    (x : Fin 5) (hcomp : Nat.card (P.complement x) = 1) :
    L ≃* Multiplicative (ZMod 5) := by
  have hfactor := (P.isComplement'_complement x).card_mul
  rw [P.degreeFive_translation_card x, hcomp, mul_one] at hfactor
  exact degreeFive_cyclicEquiv_of_card_eq_five hfactor.symm

end PrimitiveAffineProfile

namespace Non2UnipotentPrefixFiniteMenu
namespace DegreeFiveAffineClassification

/-- The published model constructor is discharged in the order-five branch.
The other two branches still require identification, not an order bound. -/
def cyclicModel
    (U : PreE7NonPairActionClass 5)
    (hcard : Nat.card (preE7NonPairAction 5 U) = 5) :
    PublishedDegreeFiveAffineModel U :=
  .cyclic (PrimitiveAffineProfile.degreeFive_cyclicEquiv_of_card_eq_five hcard)

/-- The original action has one of the three required orders, without any
use of the `PublishedDegreeFiveAffineClassification` input. -/
theorem card_cases
    (U : PreE7NonPairActionClass 5)
    (P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5)) :
    Nat.card (preE7NonPairAction 5 U) = 5 ∨
      Nat.card (preE7NonPairAction 5 U) = 10 ∨
      Nat.card (preE7NonPairAction 5 U) = 20 :=
  P.degreeFive_card_cases 0

end DegreeFiveAffineClassification
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
