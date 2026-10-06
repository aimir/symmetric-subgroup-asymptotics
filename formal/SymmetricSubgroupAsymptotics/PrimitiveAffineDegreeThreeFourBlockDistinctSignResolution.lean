import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedIsotypeSplit
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockDistinctSignSource

/-!
# Install the four-sign source in the honest sign-isotype split

The structural trichotomy formerly required three externally supplied owner
constructors.  The four-sign constructor is now internal: it is the exact
coefficient-one signed-quotient menu plus the ternary cyclic-dual bottom
tail.  Only the diagonal and two-sign constructions remain as inputs.
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

/-- Select the valid sign-isotype route, constructing the singleton route
from the actual action rather than accepting it as source data. -/
noncomputable def degreeThreeFourBlockSignedResolution_of_diagonal_twoSign
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (diagonal :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 1 →
        ComparatorAbelianTowerCertificateSourceData .s3cent w U)
    (twoSign :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 2 →
        PreE7S3TwoSource w U) :
    DegreeThreeFourBlockSignedIsotypeResolution
      block P hr hs hcomponent hbinary
        (degreeThreeFourBlockSignedIsotypeProfile
          block P hr hs hcomponent) :=
  DegreeThreeFourBlockSignedIsotypeResolution.ownerOfCases
    block P
    (degreeThreeFourBlockSignedIsotypeProfile block P hr hs hcomponent)
    diagonal twoSign
    (degreeThreeFourBlock_distinctSignExceptionalSource
      block P hr hs hcomponent hbinary)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
