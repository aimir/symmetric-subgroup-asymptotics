import SymmetricSubgroupAsymptotics.Row67OriginalQuotientSocles
import SymmetricSubgroupAsymptotics.Row67OriginalNaturalThree
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row67OriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
def jointData : DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row67Interface 1 3 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact Row67OriginalQuotientSocles.quotientSocle N.1)
  natural := Row67OriginalNaturalThree.natural_three
def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row67Interface :=
  .ofExact jointData (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row67OriginalJointData
