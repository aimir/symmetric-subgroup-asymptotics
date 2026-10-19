import SymmetricSubgroupAsymptotics.Row295OriginalPrimitiveCertificate
import SymmetricSubgroupAsymptotics.Row295OriginalElevenCycleNatural
import SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row295OriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
theorem quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row295Top) [N.Normal] : SocleNormalGeneratorBound (Row295Top ⧸ N) 1 :=
  PrimitiveTwelveFinalPublishedNormalGenerators.quotientSocle_one socle primitiveCatalogue Row295Top N

def jointData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row295Interface 1 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact quotientSocle socle primitiveCatalogue N.1)
  natural := Row295OriginalElevenCycleNatural.natural

def flexibleData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row295Interface :=
  .ofExact (jointData socle primitiveCatalogue) (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row295OriginalJointData
