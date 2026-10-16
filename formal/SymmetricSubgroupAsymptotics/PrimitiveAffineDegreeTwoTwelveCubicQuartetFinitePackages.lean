import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCentralInvolutionNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeBlockNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! Six complete original-action joint packages at admissible (2,2).
All natural fields are reused from their original checked witnesses. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveCubicQuartetFinitePackages
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row6AtTwo : DegreeTwoTwelveJointFiniteRowData row6Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles.row6AtTwo_family
  natural := PrimitiveAffineDegreeTwoTwelveCentralInvolutionNaturalFamily.row6Natural

noncomputable def row6AtTwoData : DegreeTwoTwelveFlexibleProfiles.Data row6Interface :=
  .ofExact row6AtTwo (by decide +kernel)

def row7AtTwo : DegreeTwoTwelveJointFiniteRowData row7Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles.row7AtTwo_family
  natural := PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row7Natural

noncomputable def row7AtTwoData : DegreeTwoTwelveFlexibleProfiles.Data row7Interface :=
  .ofExact row7AtTwo (by decide +kernel)

def row25AtTwo : DegreeTwoTwelveJointFiniteRowData row25Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles.row25AtTwo_family
  natural := PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row25Natural

noncomputable def row25AtTwoData : DegreeTwoTwelveFlexibleProfiles.Data row25Interface :=
  .ofExact row25AtTwo (by decide +kernel)

def row26AtTwo : DegreeTwoTwelveJointFiniteRowData row26Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles.row26AtTwo_family
  natural := PrimitiveAffineDegreeTwoTwelveCentralInvolutionNaturalFamily.row26Natural

noncomputable def row26AtTwoData : DegreeTwoTwelveFlexibleProfiles.Data row26Interface :=
  .ofExact row26AtTwo (by decide +kernel)

def row56AtTwo : DegreeTwoTwelveJointFiniteRowData row56Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles.row56AtTwo_family
  natural := DegreeTwoTwelveThreeBlockNaturalFamily.row56Natural

noncomputable def row56AtTwoData : DegreeTwoTwelveFlexibleProfiles.Data row56Interface :=
  .ofExact row56AtTwo (by decide +kernel)

def row90AtTwo : DegreeTwoTwelveJointFiniteRowData row90Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveCubicQuartetSocles.row90AtTwo_family
  natural := DegreeTwoTwelveThreeBlockNaturalFamily.row90Natural

noncomputable def row90AtTwoData : DegreeTwoTwelveFlexibleProfiles.Data row90Interface :=
  .ofExact row90AtTwo (by decide +kernel)

end DegreeTwoTwelveCubicQuartetFinitePackages
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
