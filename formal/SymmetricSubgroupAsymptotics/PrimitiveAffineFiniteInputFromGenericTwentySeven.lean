import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentySevenNonsolubleConsumers
import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentySevenSolubleConsumer

/-! The exact existing finite affine package from binary small-action
coverage and proved actual degree27 consumers. No composition-catalogue
correspondence is supplied to this factory. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

def publishedPrimitiveAffineFiniteInput_of_binary_and_genericTwentySeven
    (small : BinaryAffineSmallCatalogueData)
    (degree25 : PublishedDegreeTwentyFiveLinearData)
    (degreeEightyOne : ∀ (U : PreE7NonPairActionClass 81)
      (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
      (_hp : MulAction.IsPreprimitive (preE7NonPairAction 81 U) (Fin 81))
      (x : Fin 81), IsSolvable (P.complement x) → Nat.card (P.complement x) ≤ 81^3)
    (degreeFive : ∀ (U : PreE7NonPairActionClass 5)
      (_P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5))
      (_hp : MulAction.IsPreprimitive (preE7NonPairAction 5 U) (Fin 5)),
      PreE7SaprimDegreeFiveSource 5 U ⊕ PLift (PreE7F20Source 5 U)) :
    PublishedPrimitiveAffineFiniteInput where
  nonsolubleSmall := {
    degreeEight := fun _ P hp x T hn =>
      BinaryAffineSmallCatalogueBridge.degreeEight_abelianLength_eq_zero small _ hp P x T hn
    degreeSixteen := fun _ P hp x T hn =>
      BinaryAffineSmallCatalogueBridge.degreeSixteen_abelianLength_le_two small _ hp P x T hn
    degreeTwentyFive := degree25.nonsolubleComposition
    degreeTwentySeven := fun _ P hp x T hn =>
      primitiveAffineTwentySeven_nonsoluble_abelianLength_le_one_without_catalogue P hp x T hn }
  solubleOdd := {
    degreeTwentySeven := fun _ P hp x hs =>
      primitiveAffineTwentySeven_soluble_card_le_without_catalogue P hp x hs
    degreeEightyOne := degreeEightyOne }
  solubleCentral := {
    degreeTwentyFiveProjectiveDatum := degree25.solubleProjective }
  degreeFive := degreeFive

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
