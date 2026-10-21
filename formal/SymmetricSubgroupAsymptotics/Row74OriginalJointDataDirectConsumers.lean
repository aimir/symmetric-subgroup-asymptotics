import SymmetricSubgroupAsymptotics.Row74OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGeneratorsDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row74OriginalJointData

namespace DirectConsumers

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

 theorem normal_singletons
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    ∀ N : Subgroup row74Interface.top,N.Normal →
      ∃ x : Fin 1 → row74Interface.top,Subgroup.normalClosure (Set.range x)=N :=
  normal_generating_tuples_of_surjective
    Row74OriginalFaithfulPairTop.topEquiv.symm.toMonoidHom
    Row74OriginalFaithfulPairTop.topEquiv.symm.surjective
    (_root_.SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators.DirectConsumers.normal_generating_singletons
      socle primitiveCatalogue Row74OriginalSixPairFrame.frame.top.range)

 def jointData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row74Interface 1 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
      (_root_.SymmetricSubgroupAsymptotics.Row74OriginalJointData.DirectConsumers.normal_singletons socle primitiveCatalogue) N.1)
  natural := PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row74Natural

 def flexibleData (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveFlexibleProfiles.Data row74Interface :=
  .ofExact (_root_.SymmetricSubgroupAsymptotics.Row74OriginalJointData.DirectConsumers.jointData socle primitiveCatalogue) (by decide +kernel)

end DirectConsumers

end SymmetricSubgroupAsymptotics.Row74OriginalJointData

