import SymmetricSubgroupAsymptotics.Row220OriginalPrimitiveComponents
import SymmetricSubgroupAsymptotics.ProductTwoPrimitiveSixSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row220OriginalBlockFrame
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem quotientSocle_three
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Original) [N.Normal] : SocleNormalGeneratorBound (Original ⧸ N) 3 :=
  ProductBlockFrame.quotientSocle_three_of_two_primitive_six_components
    socle catalogue blockFrame top_surjective N

def quotientFamily
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row220Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row220Interface.normalRegistry (fun N => by
      letI := N.2
      exact quotientSocle_three socle catalogue N.1)

def jointData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row220Interface 3 1 where
  topSocle := quotientFamily socle catalogue
  natural := PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily.row220Natural

def flexibleData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row220Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (jointData socle catalogue) (by decide +kernel)

end SymmetricSubgroupAsymptotics.Row220OriginalBlockFrame
