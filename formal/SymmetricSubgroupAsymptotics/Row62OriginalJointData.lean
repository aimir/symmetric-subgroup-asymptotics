import SymmetricSubgroupAsymptotics.Row62OriginalQuotientSocles
import SymmetricSubgroupAsymptotics.Row62OriginalNaturalTwo
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row62OriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
def jointData : DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row62Interface 2 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact Row62OriginalQuotientSocles.quotientSocle N.1)
  natural := Row62OriginalNaturalTwo.natural_two
def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row62Interface :=
  .ofExact jointData (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row62OriginalJointData
