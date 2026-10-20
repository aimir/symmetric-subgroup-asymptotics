import SymmetricSubgroupAsymptotics.Row74OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGeneratorsBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row74OriginalJointData

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

 theorem normal_singletons
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    ∀ N : Subgroup row74Interface.top,N.Normal →
      ∃ x : Fin 1 → row74Interface.top,Subgroup.normalClosure (Set.range x)=N :=
  normal_generating_tuples_of_surjective
    Row74OriginalFaithfulPairTop.topEquiv.symm.toMonoidHom
    Row74OriginalFaithfulPairTop.topEquiv.symm.surjective
    (_root_.SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators.BoundedCatalogueReduced.normal_generating_singletons
      socle primitiveCatalogue Row74OriginalSixPairFrame.frame.top.range)

 def jointData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row74Interface 1 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
      (_root_.SymmetricSubgroupAsymptotics.Row74OriginalJointData.BoundedCatalogueReduced.normal_singletons socle primitiveCatalogue) N.1)
  natural := PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row74Natural

 def flexibleData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row74Interface :=
  .ofExact (_root_.SymmetricSubgroupAsymptotics.Row74OriginalJointData.BoundedCatalogueReduced.jointData socle primitiveCatalogue) (by decide +kernel)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.Row74OriginalJointData

