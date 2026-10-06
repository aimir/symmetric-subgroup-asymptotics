import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockBinaryPredicateIncidence
import SymmetricSubgroupAsymptotics.BinaryCarrierS16TaggedPositiveRoutes

/-!
# Certified routing for the binary four-block top axes

The first exact-top split retained only a bare positive `AxisSlot`.  That is
enough to state an incidence bound, but it forgets the route-local retention
certificate needed by the completed physical carrier estimate.  This module
performs the same finite degree-eight split without erasing that certificate.

The positive constructor contains one `DegreeEightRoute`; its `certified`
projection has physical half-degree four and old support four.  The only
alternative to a direct entry or such a certified positive route is the
intrinsic critical `E8` action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open BinaryCarrierCertifiedRetention
open BinaryCarrierS16TaggedPositiveRoutes
open BinaryDegreeEightCarrierSourceBridge
open BinaryDegreeEightDirectEntryCoverage
open BinaryDegreeEightPhysicalAnalyticClosure

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The exact degree-eight destination on a literal signed-quotient normal,
with the positive route retained as data rather than truncated to a bare
slot. -/
inductive DegreeThreeFourBlockBinaryCertifiedAxisChoice
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) : Type 2
  | direct : @DirectEntry8
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D) →
      DegreeThreeFourBlockBinaryCertifiedAxisChoice hr hs hcomponent D
  | positive : @DegreeEightRoute
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal
        block P hr hs hcomponent D) →
      DegreeThreeFourBlockBinaryCertifiedAxisChoice hr hs hcomponent D
  | criticalE8 : IsE8Action
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action →
      DegreeThreeFourBlockBinaryCertifiedAxisChoice hr hs hcomponent D

/-- Every literal binary top axis has a direct row, a certified positive
carrier route, or the genuine critical `E8` action. -/
noncomputable def degreeThreeFourBlockBinaryCertifiedAxisChoice
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}) :
    DegreeThreeFourBlockBinaryCertifiedAxisChoice
      block P hr hs hcomponent D := by
  letI : (degreeThreeFourBlockBinaryChartAxis
      block P hr hs hcomponent D.1).Normal :=
    degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D
  exact Classical.choice (show Nonempty
      (DegreeThreeFourBlockBinaryCertifiedAxisChoice
        block P hr hs hcomponent D) from by
    rcases degreeThreeFourBlockBinary_axis_weighted_or_carrier
        block P hr hs hcomponent hbinary
        (degreeThreeFourBlockBinaryChartAxis
          block P hr hs hcomponent D.1) with hdirect | hcarrier
    · exact ⟨.direct (Classical.choice hdirect)⟩
    · rcases degreeEightRoute_nonempty_or_e8 hcarrier with hpositive | hE8
      · exact ⟨.positive (Classical.choice hpositive)⟩
      · exact ⟨.criticalE8 hE8⟩)

/-- A positive routed axis carries the exact half-degree/support certificate
used by the reversible carrier word: four old half-points and four retained
half-points. -/
def degreeThreeFourBlockBinaryPositiveCertifiedSlot
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}}
    (R : @DegreeEightRoute
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal
        block P hr hs hcomponent D)) :
    CertifiedPositiveAxisSlot
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1) 4 :=
  letI : (degreeThreeFourBlockBinaryChartAxis
      block P hr hs hcomponent D.1).Normal :=
    degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D
  R.certified

/-- Forgetting the certificate recovers a genuine supported exact-axis slot.
This is the bridge to the predicate-preserving incidence interface. -/
def degreeThreeFourBlockBinaryPositiveAxisSlot
    {hr : Nat.card block.Fibre = 3}
    {hs : Nat.card block.Points = 4}
    {hcomponent : Nat.card block.Component = 6}
    {D : {D : Subgroup
      (preE7NonPairAction w U ⧸ E block P) // D.Normal}}
    (R : @DegreeEightRoute
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1)
      (degreeThreeFourBlockBinaryChartAxisNormal
        block P hr hs hcomponent D)) :
    {S : AxisSlot
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
      (degreeThreeFourBlockBinaryChartAxis block P hr hs hcomponent D.1) //
      S.HasNoncritical} :=
  letI : (degreeThreeFourBlockBinaryChartAxis
      block P hr hs hcomponent D.1).Normal :=
    degreeThreeFourBlockBinaryChartAxisNormal block P hr hs hcomponent D
  ⟨R.certified.axisSlot, R.certified.hasNoncritical⟩

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
