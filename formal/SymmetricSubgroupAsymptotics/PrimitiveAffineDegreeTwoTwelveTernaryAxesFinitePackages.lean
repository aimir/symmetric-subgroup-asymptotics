import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryAxesImageFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily

/-! Four original alternate (3,1) packages share the two-axis image theorem.
The checked row159 pilot is reused; three further natural bounds are
supplied by their existing exact original-action proofs. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveTernaryAxesFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row159At3 : DegreeTwoTwelveJointFiniteRowData row159Interface 3 1 :=
  DegreeTwoTwelveTernaryAxesImagePilot.row159At3
noncomputable def row159At3Data : DegreeTwoTwelveFlexibleProfiles.Data row159Interface :=
  DegreeTwoTwelveTernaryAxesImagePilot.row159At3Data

/-- Original row196, index195, joint; historical (2,1). -/
def row196At3 : DegreeTwoTwelveJointFiniteRowData row196Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveTernaryAxesImageFamily.row196AtThree_family
    PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily.row196Natural
  natural := PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily.row196Natural

noncomputable def row196At3Data : DegreeTwoTwelveFlexibleProfiles.Data row196Interface :=
  .ofExact row196At3 (by decide +kernel)

/-- Original row197, index196, joint; historical (2,1). -/
def row197At3 : DegreeTwoTwelveJointFiniteRowData row197Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveTernaryAxesImageFamily.row197AtThree_family
    PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily.row197Natural
  natural := PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily.row197Natural

noncomputable def row197At3Data : DegreeTwoTwelveFlexibleProfiles.Data row197Interface :=
  .ofExact row197At3 (by decide +kernel)

/-- Original row240, index239, joint; historical (3,1). -/
def row240At3 : DegreeTwoTwelveJointFiniteRowData row240Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveTernaryAxesImageFamily.row240AtThree_family
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily.row240Natural
  natural := SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily.row240Natural

noncomputable def row240At3Data : DegreeTwoTwelveFlexibleProfiles.Data row240Interface :=
  .ofExact row240At3 (by decide +kernel)

end DegreeTwoTwelveTernaryAxesFinitePackages
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
