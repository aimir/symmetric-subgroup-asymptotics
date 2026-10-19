import SymmetricSubgroupAsymptotics.Row179SharedPrimitiveCertificate
import SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveElevenCycleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Original row179 and its literal-tuple overgroup row218 at (1,1).
The shared point-word witness proves actual primitivity; the existing two
published primitive inputs then retain every original normal denominator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem row179_quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row179Top) [N.Normal] : SocleNormalGeneratorBound (Row179Top ⧸ N) 1 :=
  PrimitiveTwelveFinalPublishedNormalGenerators.quotientSocle_one socle catalogue Row179Top N

theorem row218_quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Row218Top) [N.Normal] : SocleNormalGeneratorBound (Row218Top ⧸ N) 1 :=
  PrimitiveTwelveFinalPublishedNormalGenerators.quotientSocle_one socle catalogue Row218Top N

def row179Family
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row179Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row179Interface.normalRegistry (fun N => by letI := N.2; exact row179_quotientSocle socle catalogue N.1)
def row218Family
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row218Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row218Interface.normalRegistry (fun N => by letI := N.2; exact row218_quotientSocle socle catalogue N.1)

def row179Data
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row179Interface 1 1 where
  topSocle := row179Family socle catalogue
  natural := PrimitiveAffineDegreeTwoTwelveElevenCycleNaturalFamily.row179Natural
def row218Data
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row218Interface 1 1 where
  topSocle := row218Family socle catalogue
  natural := PrimitiveAffineDegreeTwoTwelveElevenCycleNaturalFamily.row218Natural

def row179Flexible
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row179Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (row179Data socle catalogue) (by decide +kernel)
def row218Flexible
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row218Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (row218Data socle catalogue) (by decide +kernel)

end SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData
