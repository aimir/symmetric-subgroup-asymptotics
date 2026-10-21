import SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSoclesDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData

namespace DirectConsumers

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def jointData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (C : DegreeTwoPairTopFiniteInterface 12)
    (F : BinaryPairFrame C.top (Fin 6))
    [MulAction.IsPretransitive F.top.range (Fin 6)]
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) C.top (Fin 12)) 1) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData C 3 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    C.normalRegistry (fun N => by
      letI := N.2
      exact _root_.SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSocles.DirectConsumers.quotientSocle socle catalogue F hnatural N.1)
  natural := hnatural

end DirectConsumers

end SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData

