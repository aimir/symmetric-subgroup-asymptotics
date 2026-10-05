import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductLiteralEnvelope

/-!
# Action-facing central-product source at an arbitrary original width

The correlated central-repeat estimate is a theorem about the literal finite
group, not about its chosen permutation representation.  This file performs
the only action-facing step: it bounds every accepted source by the complete
quotient weight of the unchanged original group and then applies the literal
summed envelope.  The comparator remains the checked five-point action of
the quotient by the central binary axis.

This wrapper is used at width six by the three-pair catalogue and can be
reused unchanged for the `A4 x C2` and `S4 x C2` rows at width eight.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PreE7CentralProductRankTailData

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  (D : PreE7CentralProductRankTailData (preE7NonPairAction w U))

/-- Install the literal complete-weight envelope on an arbitrary faithful
permutation representation of its original group.  No width-dependent
estimate is used here; numerical pointing is deliberately left to the
consumer. -/
noncomputable def pairSummedSource :
    PreE7DegreeTwoPairSummedSource w U where
  R := preE7NonPairAction w U ⧸ D.E
  v := 5
  action := D.action
  action_injective := D.action_injective
  mainCoefficient := normalCount D
  coldCoefficient := fun _ => normalCount D * D.lowerConstant
  eta := 0
  theta := 3 / 5
  mainCoefficient_nonneg := normalCount_nonneg D
  coldCoefficient_nonneg := fun _ =>
    mul_nonneg (normalCount_nonneg D) D.lowerConstant_nonneg
  exceptionalRaw := D.literalExceptionalEnvelope
  exceptionalRaw_nonneg := D.literalExceptionalEnvelope_nonneg
  summed := fun b P => by
    apply (Finset.sum_le_sum (fun J _ => ?_)).trans
      (D.quotientSummedEnvelope.summed b)
    unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun N _ =>
      fusionSurvivingEpiCount_le_groupEpimorphism_card
        (preE7NonPairAction w U) P N J)

end PreE7CentralProductRankTailData
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
