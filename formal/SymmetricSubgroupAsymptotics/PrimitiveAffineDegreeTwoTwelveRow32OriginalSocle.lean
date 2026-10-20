import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32OriginalPairSection
import SymmetricSubgroupAsymptotics.TernaryOddPartPairSectionSocle
import SymmetricSubgroupAsymptotics.TernarySemiregularS3QuotientAnchor

/-!
# The literal row-32 nonbinary quotient socle

The original pair section supplies multiplicity two for every scalar
degree-two simple type. Its actual top image has order dividing forty-eight.
The original 24-point sectional rank and ternary centralizer geometry
discharge the dimension and fixed-rank inputs. The resulting four normal
socle generators give one ordinary and three relative slots using only
the existing published whole-socle Zmud input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow32OriginalSocle

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoTwelveRow32OriginalGeometry

variable {p : PreE7PairActionClass 12}
  (R : DegreeTwoPairTopRealization DegreeTwoTwelvePairFiniteCatalogue.row32Interface p)

include R in
theorem nonbinary_quotient_socleGeneratorBound
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hQ : ¬ IsPGroup 2 (preE7PairAction 12 p ⧸ N.1)) :
    SocleNormalGeneratorBound (preE7PairAction 12 p ⧸ N.1) 4 := by
  letI : N.1.Normal := N.2
  letI : IsSolvable (preE7PairAction 12 p) := original_solvable R
  letI : IsSolvable (preE7PairAction 12 p ⧸ N.1) :=
    solvable_of_surjective (QuotientGroup.mk'_surjective N.1)
  have hsection : PrimeSectionalRankBound 2 (preE7PairAction 12 p ⧸ N.1) 12 := by
    simpa only [Nat.card_fin] using
      binarySectionalRankBound_of_faithful_permutation_quotient (X := Fin 24)
        (QuotientGroup.mk' N.1) (QuotientGroup.mk'_surjective N.1)
  have hcentral := nonbinary_quotient_central_finrank_le_four R N hQ
  have hrange : Nat.card R.frame.top.range = 48 :=
    (Nat.card_congr R.topEquiv.toEquiv).symm.trans top_card
  have hcardB : Nat.card (preE7PairAction 12 p ⧸ (R.frame.top.ker ⊔ N.1)) ∣ 48 := by
    have h := Subgroup.card_dvd_of_surjective (R.frame.sectionTopQuotient N.1)
      (R.frame.sectionTopQuotient_surjective N.1)
    rwa [hrange] at h
  obtain ⟨a, ha⟩ := original_card R
  have hcardQ : Nat.card (preE7PairAction 12 p ⧸ N.1) ∣ 2 ^ a * 3 := by
    simpa only [ha] using N.1.card_quotient_dvd_card
  apply socleNormalGeneratorBound_four_of_isSolvable_pairSection
    (R.frame.zeroCutBase N.1) (R.frame.sectionModuleChart N.1)
    hsection hcentral hcardB ?_ hcardQ
  intro W _ _ _ sigma _ hdim hEnd
  exact PrimitiveAffineDegreeTwoTwelveRow32OriginalPairSection.section_multiplicity_le_two
    R N.1 sigma hdim hEnd

/-- No rank, multiplicity, module-state, or new feasibility premise remains
for this actual original quotient. -/
def nonbinary_quotient_anchor (hZmud : ZmudFaithfulCharacterTupleInput)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hQ : ¬ IsPGroup 2 (preE7PairAction 12 p ⧸ N.1)) :
    DegreeTwoPairRelativeKernelAnchor (preE7PairAction 12 p ⧸ N.1)
      (degreeTwoPairOrdinaryRelativeProfile 1 3) := by
  letI : N.1.Normal := N.2
  let a := (original_card R).choose
  have ha : Nat.card (preE7PairAction 12 p) = 2 ^ a * 3 :=
    (original_card R).choose_spec
  have hdiv : Nat.card (preE7PairAction 12 p ⧸ N.1) ∣ 2 ^ a * 3 := by
    simpa only [ha] using N.1.card_quotient_dvd_card
  let orderData := ternaryOddPart_exists_card_eq_of_not_isPGroup_two hdiv hQ
  exact DegreeTwoPairRelativeKernelAnchor.ofTernaryOddPartSocleGeneratorBound
    hZmud orderData.choose_spec.2 (nonbinary_quotient_socleGeneratorBound R N hQ)

end PrimitiveAffineDegreeTwoTwelveRow32OriginalSocle
end SymmetricSubgroupAsymptotics

end
