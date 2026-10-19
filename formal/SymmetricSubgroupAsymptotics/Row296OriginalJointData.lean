import SymmetricSubgroupAsymptotics.Row296OriginalPrimitiveComponents
import SymmetricSubgroupAsymptotics.ProductTwoPrimitiveSixSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row296OriginalBlockFrame
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem top_surjective : Function.Surjective blockFrame.top := by
  intro q
  have hq : q = 1 ∨ q = swap :=
    (show ∀ q : Equiv.Perm (Fin 2), q = 1 ∨ q = swap from by decide +kernel) q
  rcases hq with rfl | rfl
  · exact ⟨1,map_one _⟩
  · exact ⟨originalGenerator 2,top_generator 2⟩

theorem quotientSocle_three
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Original) [N.Normal] : SocleNormalGeneratorBound (Original ⧸ N) 3 :=
  ProductBlockFrame.quotientSocle_three_of_two_primitive_six_components
    socle catalogue blockFrame top_surjective N

def quotientFamily
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row296Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row296Interface.normalRegistry (fun N => by
      letI := N.2
      exact quotientSocle_three socle catalogue N.1)

def jointData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row296Interface 3 1 where
  topSocle := quotientFamily socle catalogue
  natural := PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row296Natural

def flexibleData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row296Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (jointData socle catalogue) (by decide +kernel)

end SymmetricSubgroupAsymptotics.Row296OriginalBlockFrame
