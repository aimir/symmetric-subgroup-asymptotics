import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageMoreSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeBlockNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDihedralPairImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLocalWreathPairImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOddPairCycleWordNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOppositeCyclePairImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily

/-! Twelve original joint actions share actual six-pair image bounds.
Eight retain their historical capacities. Four use different, proved capacities
within the same numerical menu; these do not assert historical profile equality.
The natural-module and quotient-socle fields concern the same literal action. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairImageFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row145At3 : DegreeTwoTwelveJointFiniteRowData row145Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveDihedralPairImageSocles.row145AtThree_family
  natural := PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily.row145Natural

noncomputable def row145At3Data :
    DegreeTwoTwelveFlexibleProfiles.Data row145Interface :=
  .ofExact row145At3 (by decide +kernel)

def row193 : DegreeTwoTwelveJointFiniteRowData row193Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveDihedralPairImageSocles.row193_family
  natural := PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily.row193Natural

noncomputable def row193Data :
    DegreeTwoTwelveFlexibleProfiles.Data row193Interface :=
  .ofExact row193 (by decide +kernel)

def row69At2 : DegreeTwoTwelveJointFiniteRowData row69Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageSocles.row69AtTwo_family
  natural := PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily.row69Natural

noncomputable def row69At2Data :
    DegreeTwoTwelveFlexibleProfiles.Data row69Interface :=
  .ofExact row69At2 (by decide +kernel)

def row107At2 : DegreeTwoTwelveJointFiniteRowData row107Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageSocles.row107AtTwo_family
  natural := PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily.row107Natural

noncomputable def row107At2Data :
    DegreeTwoTwelveFlexibleProfiles.Data row107Interface :=
  .ofExact row107At2 (by decide +kernel)

def row135 : DegreeTwoTwelveJointFiniteRowData row135Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageSocles.row135_family
  natural := PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily.row135Natural

noncomputable def row135Data :
    DegreeTwoTwelveFlexibleProfiles.Data row135Interface :=
  .ofExact row135 (by decide +kernel)

def row235 : DegreeTwoTwelveJointFiniteRowData row235Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveLocalWreathPairImageSocles.row235_family
  natural := PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily.row235Natural

noncomputable def row235Data :
    DegreeTwoTwelveFlexibleProfiles.Data row235Interface :=
  .ofExact row235 (by decide +kernel)

def row60At2 : DegreeTwoTwelveJointFiniteRowData row60Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveOppositeCyclePairImageSocles.row60AtTwo_family
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row60Natural

noncomputable def row60At2Data :
    DegreeTwoTwelveFlexibleProfiles.Data row60Interface :=
  .ofExact row60At2 (by decide +kernel)

def row89 : DegreeTwoTwelveJointFiniteRowData row89Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveOppositeCyclePairImageSocles.row89_family
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row89Natural

noncomputable def row89Data :
    DegreeTwoTwelveFlexibleProfiles.Data row89Interface :=
  .ofExact row89 (by decide +kernel)

def row91 : DegreeTwoTwelveJointFiniteRowData row91Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveOppositeCyclePairImageSocles.row91_family
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row91Natural

noncomputable def row91Data :
    DegreeTwoTwelveFlexibleProfiles.Data row91Interface :=
  .ofExact row91 (by decide +kernel)

def row143 : DegreeTwoTwelveJointFiniteRowData row143Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveOppositeCyclePairImageSocles.row143_family
  natural := PrimitiveAffineDegreeTwoTwelveOddPairCycleWordNaturalFamily.row143Natural

noncomputable def row143Data :
    DegreeTwoTwelveFlexibleProfiles.Data row143Interface :=
  .ofExact row143 (by decide +kernel)

def row3 : DegreeTwoTwelveJointFiniteRowData row3Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageMoreSocles.row3_family
  natural := PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row3Natural

noncomputable def row3Data :
    DegreeTwoTwelveFlexibleProfiles.Data row3Interface :=
  .ofExact row3 (by decide +kernel)

def row106 : DegreeTwoTwelveJointFiniteRowData row106Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRegularSymmetricPairImageMoreSocles.row106_family
  natural := DegreeTwoTwelveThreeBlockNaturalFamily.row106Natural

noncomputable def row106Data :
    DegreeTwoTwelveFlexibleProfiles.Data row106Interface :=
  .ofExact row106 (by decide +kernel)

end DegreeTwoTwelvePairImageFinitePackages
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
