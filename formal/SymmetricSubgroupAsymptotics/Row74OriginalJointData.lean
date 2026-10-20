import SymmetricSubgroupAsymptotics.Row74OriginalFaithfulPairTop
import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratingTuplesExtension
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row74OriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

 theorem normal_singletons
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    ∀ N : Subgroup row74Interface.top,N.Normal →
      ∃ x : Fin 1 → row74Interface.top,Subgroup.normalClosure (Set.range x)=N :=
  normal_generating_tuples_of_surjective
    Row74OriginalFaithfulPairTop.topEquiv.symm.toMonoidHom
    Row74OriginalFaithfulPairTop.topEquiv.symm.surjective
    (PrimitiveSixFinalPublishedNormalGenerators.normal_generating_singletons
      socle primitiveCatalogue Row74OriginalSixPairFrame.frame.top.range)

 def jointData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row74Interface 1 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
      (normal_singletons socle primitiveCatalogue) N.1)
  natural := PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row74Natural

 def flexibleData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row74Interface :=
  .ofExact (jointData socle primitiveCatalogue) (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row74OriginalJointData
