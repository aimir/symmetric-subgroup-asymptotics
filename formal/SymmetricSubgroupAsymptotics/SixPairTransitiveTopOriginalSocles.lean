import SymmetricSubgroupAsymptotics.TransitiveSixNormalGenerators

/-! A checked uniform natural-module bound on the original action and an
actual physical six-pair frame give the original normal-quotient socle bound
three. The top normal bound is derived for the actual transitive image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSocles
open Non2UnipotentPrefixFiniteMenu

theorem quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
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
  exact TransitiveSixNormalGenerators.normalGen_le_two socle catalogue F.top.range L

end SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSocles
