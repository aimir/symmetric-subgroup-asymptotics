import SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSocles
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorsDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSocles

namespace DirectConsumers

open Non2UnipotentPrefixFiniteMenu

theorem quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 6))
    [MulAction.IsPretransitive F.top.range (Fin 6)]
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 1)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 := by
  apply F.quotientSocle_of_uniform_pair_action 1 2
    (F.uniform_pair_action_of_original 1 hnatural) ?_ N
  intro L hL
  letI := hL
  exact _root_.SymmetricSubgroupAsymptotics.TransitiveSixNormalGenerators.DirectConsumers.normalGen_le_two socle catalogue F.top.range L

end DirectConsumers

end SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSocles

