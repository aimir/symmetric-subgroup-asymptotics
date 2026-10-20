import SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSocles
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorsBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSocles

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

theorem quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
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
  exact _root_.SymmetricSubgroupAsymptotics.TransitiveSixNormalGenerators.BoundedCatalogueReduced.normalGen_le_two socle catalogue F.top.range L

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSocles

