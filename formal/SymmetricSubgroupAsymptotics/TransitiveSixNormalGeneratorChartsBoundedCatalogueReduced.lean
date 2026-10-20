import SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorCharts
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGeneratorsBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

open scoped Pointwise Classical

namespace SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorCharts

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

theorem normal_generating_pairs
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive P (Fin 6)]
    (C : Chart P) : ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 2 → P, Subgroup.normalClosure (Set.range x) = N := by
  cases C with
  | primitive hp =>
      letI := hp
      intro N hN
      letI := hN
      apply exists_normal_generating_tuple_of_normalGen_le N
      exact (_root_.SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators.BoundedCatalogueReduced.normalGen_le_one socle catalogue P N).trans (by decide)
  | threePairs frame =>
      intro N hN
      letI := hN
      exact exists_normal_generating_tuple_of_normalGen_le N
        (ThreePairNormalGenerators.normalGen_le_of_transitive frame N)
  | axes c hle =>
      let e : P ≃* (MulAut.conj c • P : Subgroup (Equiv.Perm (Fin 6))) := actionConjugacyEquiv c rfl
      exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
        (SixPointTernaryAxesNormalGenerators.normal_generating_pairs _ hle)
  | quarter c hle lift hmem hupper =>
      let e : P ≃* (MulAut.conj c • P : Subgroup (Equiv.Perm (Fin 6))) := actionConjugacyEquiv c rfl
      exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
        (SixPointTernaryQuarterTurnNormalGenerators.normal_generating_pairs _ hle lift hmem hupper)
  | fullWreath c heq =>
      let e : P ≃* SixPairLocalWreathSocles.literalAction.range := actionConjugacyEquiv c heq
      apply normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
      intro N hN
      letI := hN
      exact exists_normal_generating_tuple_of_normalGen_le N
        (SixPairLocalWreathSocles.image_normalGen N hN)

theorem quotientSocle_of_original_natural
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 6))
    [MulAction.IsPretransitive F.top.range (Fin 6)]
    (C : Chart F.top.range)
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 1)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 := by
  apply F.quotientSocle_of_uniform_pair_action 1 2
    (F.uniform_pair_action_of_original 1 hnatural) ?_ N
  intro L hL
  letI := hL
  obtain ⟨x,hx⟩ := _root_.SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorCharts.BoundedCatalogueReduced.normal_generating_pairs socle catalogue F.top.range C L hL
  exact normalGen_le_of_fin_tuple x hx

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.TransitiveSixNormalGeneratorCharts

