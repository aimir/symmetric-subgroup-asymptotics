import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignOrderFourComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignTopRecognition

/-!
# Complete projective comparison in the four-block two-sign branch

The literal projective top has order four or eight.  The order-four branch
uses the uniform central binary recursion; the order-eight branch fills the
literal two-pair preserving group and is therefore `D₈`.  Both actual
signed quotients are controlled by the fixed degree-ten comparator with a
single coefficient `2^128`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev PairChart
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :=
  degreeThreeFourBlockPairChart block P hr hs hcomponent

/-- Uniform complete-weight comparison for the actual two-sign signed
quotient, with the order-four and order-eight projective tops dispatched
from the literal pair frame. -/
theorem degreeThreeFourBlockTwoSign_signedQuotient_completeWeight_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight
        (R := DegreeThreeFourBlockTwoSignSignedQuotient block P) J ≤
      (2 ^ 128 : ℝ) * completeQuotientWeight
        (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
  rcases degreeThreeFourBlockTwoSign_top_card_cases
      block P hr hs hcomponent hbinary with htop | htop
  · let D := degreeThreeFourBlockTwoSign_signedQuotientOrderFourComparison
      block P hr hs hcomponent hbinary htwo htop
    calc
      completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignSignedQuotient block P) J ≤
        (D.coefficient : ℝ) * completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J :=
        degreeThreeFourBlockTwoSign_signedQuotient_completeWeight_le_of_top_card_four
          block P hr hs hcomponent hbinary htwo htop J
      _ ≤ (2 ^ 128 : ℝ) * completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast
            degreeThreeFourBlockTwoSign_signedQuotientOrderFourCoefficient_le
              block P hr hs hcomponent hbinary htwo htop
        · exact completeQuotientWeight_nonneg J
  · let topEquiv :=
      degreeThreeFourBlockTwoSign_topEquivD8_of_card_eight
        block P hr hs hcomponent htwo htop
    let D := degreeThreeFourBlockTwoSign_signedQuotientD8Comparison
      block P hr hs hcomponent hbinary htwo topEquiv
    calc
      completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignSignedQuotient block P) J ≤
        (D.coefficient : ℝ) * completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J :=
        degreeThreeFourBlockTwoSign_signedQuotient_completeWeight_le_of_topEquivD8
          block P hr hs hcomponent hbinary htwo topEquiv J
      _ ≤ (2 ^ 128 : ℝ) * completeQuotientWeight
          (R := DegreeThreeFourBlockTwoSignComparator.QStar) J := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast
            (degreeThreeFourBlockTwoSign_signedQuotientD8Coefficient_le
              block P hr hs hcomponent hbinary htwo topEquiv).trans
              (Nat.pow_le_pow_right (by norm_num) (by omega))
        · exact completeQuotientWeight_nonneg J

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
