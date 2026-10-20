import SymmetricSubgroupAsymptotics.Row200SixPairOriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointDataBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row200SixPairOriginalJointData

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

def flexibleData (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row200Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (_root_.SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData.BoundedCatalogueReduced.jointData socle catalogue row200Interface pairFrame
      DegreeTwoTwelveRow17NaturalFamily.row200Natural) (by decide +kernel)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.Row200SixPairOriginalJointData

