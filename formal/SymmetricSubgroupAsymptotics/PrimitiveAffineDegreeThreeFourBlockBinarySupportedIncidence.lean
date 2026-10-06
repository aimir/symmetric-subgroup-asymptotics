import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockBinaryCertifiedRouting
import SymmetricSubgroupAsymptotics.BinaryCarrierAxisSlotComparator

/-!
# Positive-carrier incidence in the binary four-block cell

For a fixed literal signed-quotient top normal, a supported carrier slot
identifies the top quotient with one normal quotient of the *same retained
proper carrier*.  Multiplying by the exact elementary-layer top contribution
therefore preserves the annihilator/carrier correlation.  This is the local
positive branch required before the finite route menu is aggregated.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open BinaryCarrierAxisSlotComparator
open BinaryDegreeEightPhysicalAnalyticClosure

variable {w b : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- A supported exact slot bounds the accepted top fibre by its own carrier
quotient moment times the literal fixed-top elementary contribution. -/
theorem degreeThreeFourBlockBinaryAcceptedTopTerm_supported_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    (S : AxisSlot
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)) :
    degreeThreeFourBlockBinaryAcceptedTopTerm block P source J D ≤
      completeQuotientWeight (R := S.slot.carrier) J *
        elementaryLayerExactTopContribution
          (elementaryChart block P).p
          (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P))
          (elementaryChart block P).quotientRepresentation
          (elementaryChart block P).originalKernelChart D b := by
  letI : (degreeThreeFourBlockBinaryChartAxis
      block P hr hs hcomponent D.1).Normal :=
    degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D
  have htop :
      (Nat.card (GroupEpimorphism J
        ((degreeThreeFourBlockPairChart block P hr hs hcomponent).action ⧸
          degreeThreeFourBlockBinaryChartAxis
            block P hr hs hcomponent D.1)) : ℝ) ≤
        completeQuotientWeight (R := S.slot.carrier) J :=
    epi_card_le_completeQuotientWeight S J
  have hfactor := elementaryLayerExactTopContribution_nonneg
    (elementaryChart block P).p
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (elementaryChart block P).originalKernelChart D b
  exact (degreeThreeFourBlockBinaryAcceptedTopTerm_le_jointTopTerm
    block P hr hs hcomponent hbinary source J D).trans (by
      unfold degreeThreeFourBlockBinaryJointTopTerm
      exact mul_le_mul_of_nonneg_right htop hfactor)

/-- The retained `DegreeEightRoute` supplies the same estimate together with
the exact positive-support certificate used by later physical aggregation. -/
theorem degreeThreeFourBlockBinaryAcceptedTopTerm_positiveRoute_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal})
    (R : @BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal
        block P hr hs hcomponent D)) :
    degreeThreeFourBlockBinaryAcceptedTopTerm block P source J D ≤
      completeQuotientWeight
          (R := (@BinaryCarrierS16TaggedPositiveRoutes.DegreeEightRoute.certified
            _ _ (degreeThreeFourBlockBinaryChartAxisNormal
              block P hr hs hcomponent D) R).axisSlot.slot.carrier) J *
        elementaryLayerExactTopContribution
          (elementaryChart block P).p
          (QuotientGroup.mk' (E block P))
          (QuotientGroup.mk'_surjective (E block P))
          (elementaryChart block P).quotientRepresentation
          (elementaryChart block P).originalKernelChart D b := by
  letI : (degreeThreeFourBlockBinaryChartAxis
      block P hr hs hcomponent D.1).Normal :=
    degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D
  exact degreeThreeFourBlockBinaryAcceptedTopTerm_supported_le
    block P hr hs hcomponent hbinary source J D R.certified.axisSlot

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
