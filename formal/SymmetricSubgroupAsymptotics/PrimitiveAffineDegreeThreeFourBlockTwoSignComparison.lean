import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignBottomComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignProjectiveDispatch
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockFullTranslationTail
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedDispatcher

/-!
# Concrete two-sign four-block comparison

The literal translation rank is two or four.  In rank two, the whole
bottom is compared with `QStar`; in rank four, the existing cyclic-dual
tail handles the bottom.  The signed quotient and every proper section use
the already proved uniform `QStar` comparisons.  This closes the exact
two-sign source boundary used by the degree-three dispatcher.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Concrete construction of every two-sign four-block comparison from the
literal affine data alone. -/
noncomputable def degreeThreeFourBlockTwoSignComparisonSource :
    DegreeThreeFourBlockTwoSignComparisonSource := by
  intro w U basePoint block P _ hr hs hcomponent hbinary htwo
  rcases degreeThreeFourBlockTwoSign_translation_finrank_eq_two_or_four
      block P hr hs hcomponent hbinary htwo with hfin | hfin
  · exact degreeThreeFourBlockTwoSignComparison_of_literalBounds
      block P
      (2 ^ 200 : ℝ)
      (2 ^ 128 : ℝ)
      (fun _ => (2 ^ 200 : ℝ))
      0
      (by positivity)
      (by positivity)
      (fun _ => by positivity)
      (by norm_num)
      (fun J =>
        degreeThreeFourBlockTwoSign_signedQuotient_completeWeight_le
          block P hr hs hcomponent hbinary htwo J)
      (fun N J =>
        degreeThreeFourBlockTwoSignSection_bundledWeight_le
          block P hr hs hcomponent hbinary htwo N J)
      (fun J => by
        simpa only [zero_mul, add_zero] using
          degreeThreeFourBlockTwoSignBottom_epimorphism_card_le
            block P hr hs hcomponent hbinary htwo hfin J)
      (twoSign_uniform_mainCoefficient_le (E block P)
        (degreeThreeFourBlock_twoSign_order_le
          block P hr hs hcomponent hbinary htwo))
      (by norm_num)
  · let tailCoefficient : ℝ :=
      Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U)
    exact degreeThreeFourBlockTwoSignComparison_of_literalBounds
      block P
      (2 ^ 200 : ℝ)
      (2 ^ 128 : ℝ)
      (fun _ => (2 ^ 200 : ℝ))
      tailCoefficient
      (by positivity)
      (by positivity)
      (fun _ => by positivity)
      (Nat.cast_nonneg _)
      (fun J =>
        degreeThreeFourBlockTwoSign_signedQuotient_completeWeight_le
          block P hr hs hcomponent hbinary htwo J)
      (fun N J =>
        degreeThreeFourBlockTwoSignSection_bundledWeight_le
          block P hr hs hcomponent hbinary htwo N J)
      (fun J => by
        have htail := degreeThreeFourBlock_fullTranslation_tail
          block P hr hs hcomponent hbinary hfin J
        calc
          (Nat.card (GroupEpimorphism J
              (preE7NonPairAction w U)) : ℝ) ≤
              tailCoefficient *
                (2 : ℝ) ^ ((Real.logb 2 3 / 3) * _) := by
            simpa only [tailCoefficient] using htail
          _ ≤ (2 ^ 200 : ℝ) *
                completeQuotientWeight
                  (R := DegreeThreeFourBlockTwoSignComparator.QStar) J +
              tailCoefficient *
                (2 : ℝ) ^ ((Real.logb 2 3 / 3) * _) := by
            exact le_add_of_nonneg_left
              (mul_nonneg (by positivity)
                (completeQuotientWeight_nonneg J)))
      (twoSign_uniform_mainCoefficient_le (E block P)
        (degreeThreeFourBlock_twoSign_order_le
          block P hr hs hcomponent hbinary htwo))
      (by
        simpa only [tailCoefficient] using
          degreeThreeFourBlock_twoSign_fullTranslation_aut_le
            block P hr hs hcomponent hbinary htwo hfin)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
