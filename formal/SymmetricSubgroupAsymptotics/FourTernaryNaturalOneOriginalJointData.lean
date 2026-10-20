import SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalFrames
import SymmetricSubgroupAsymptotics.ProductBlockFrameFourTernarySocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open FourTernaryNaturalOneOriginalFrames

private def jointData (C : DegreeTwoPairTopFiniteInterface 12)
    (F : ProductBlockFrame C.top (Fin 4) (Fin 3))
    (heven : alternatingGroup (Fin 4) ≤ F.top.range)
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) C.top (Fin 12)) 1) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData C 3 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    C.normalRegistry (fun N => by
      letI := N.2
      exact F.quotientSocle_three_of_four_ternary_blocks heven N.1)
  natural := hnatural

def row122Data (_socle : PublishedPrimitiveSocleDichotomyInput)
    (_catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row122Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (jointData row122Interface (frame 0) (alternating_le 0)
      PrimitiveAffineDegreeTwoTwelveTernaryAlternatingNaturalFamily.row122Natural) (by decide +kernel)
def row157Data (_socle : PublishedPrimitiveSocleDichotomyInput)
    (_catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row157Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (jointData row157Interface (frame 1) (alternating_le 1)
      PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row157Natural) (by decide +kernel)
def row213Data (_socle : PublishedPrimitiveSocleDichotomyInput)
    (_catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row213Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (jointData row213Interface (frame 2) (alternating_le 2)
      DegreeTwoTwelveRow72PolynomialFamily.row213Natural) (by decide +kernel)
def row232Data (_socle : PublishedPrimitiveSocleDichotomyInput)
    (_catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row232Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (jointData row232Interface (frame 3) (alternating_le 3)
      PrimitiveAffineDegreeTwoTwelveTernaryAlternatingNaturalFamily.row232Natural) (by decide +kernel)
def row259Data (_socle : PublishedPrimitiveSocleDichotomyInput)
    (_catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row259Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (jointData row259Interface (frame 4) (alternating_le 4)
      PrimitiveAffineDegreeTwoTwelveTernaryAlternatingNaturalFamily.row259Natural) (by decide +kernel)

end SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalJointData
