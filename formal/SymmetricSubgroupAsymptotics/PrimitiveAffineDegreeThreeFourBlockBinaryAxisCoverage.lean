import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockPairPackage
import SymmetricSubgroupAsymptotics.BinaryDegreeEightDirectEntryCoverage

/-!
# Literal binary-axis coverage in the degree-three four-block cell

When the signed quotient is a binary group, its canonical four-pair chart
is a transitive binary degree-eight action.  The checked degree-eight
registry therefore applies on every literal normal axis.  This file keeps
that conclusion on the actual signed quotient chart: each axis has either
an original-weight direct entry or one of the exact routed carrier slots.

This is the structural half of the coupled ternary/binary estimate.  It
does not erase the axis into a complete-quotient envelope and does not claim
that the ternary prepend is independent of the binary row.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open BinaryDegreeEightDirectEntryCoverage
open BinaryDegreeEightPhysicalAnalyticClosure

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private theorem degreeThreeFourBlockPairChart_transitive
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    PermutationSubgroupTransitive
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  intro x y
  obtain ⟨g, hg⟩ := C.pretransitive.exists_smul_eq x y
  exact ⟨g, g.2, hg⟩

/-- Every normal axis of the actual binary signed quotient reaches the
checked degree-eight direct-entry or exact-carrier interface. -/
theorem degreeThreeFourBlockBinary_axis_weighted_or_carrier
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (N : Subgroup
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    [N.Normal] :
    Nonempty (DirectEntry8
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action N) ∨
      CarrierOwner
        (degreeThreeFourBlockPairChart block P hr hs hcomponent).action N :=
  complete_axis_weighted_or_carrier
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
    hbinary
    (degreeThreeFourBlockPairChart_transitive block P hr hs hcomponent)
    N

/-- Counting-facing variant with every carrier branch already pulled back
to an exact literal axis slot on the signed quotient chart. -/
theorem degreeThreeFourBlockBinary_axis_direct_or_slot
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (N : Subgroup
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    [N.Normal] :
    DirectOwner
        (degreeThreeFourBlockPairChart block P hr hs hcomponent).action N ∨
      Nonempty (AxisSlot
        (degreeThreeFourBlockPairChart block P hr hs hcomponent).action N) :=
  complete_axis_direct_or_slot
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
    hbinary
    (degreeThreeFourBlockPairChart_transitive block P hr hs hcomponent)
    N

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
