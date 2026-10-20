import SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open PrimitiveTwelveExactProfileNormalGenerators

theorem normal_generating_singletons
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPreprimitive P (Fin 12)] :
    ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 1 → P, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨U,c,hc,hp,⟨D⟩⟩ := exists_exact_profile socle P
  letI := hp
  let e : P ≃* preE7NonPairAction 12 U := actionConjugacyEquiv c hc
  exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
    (catalogue.normal_generating_singletons D (Or.inr rfl))

theorem normalGen_le_one
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPreprimitive P (Fin 12)]
    (N : Subgroup P) [N.Normal] : MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨x,hx⟩ := _root_.SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators.BoundedCatalogueReduced.normal_generating_singletons socle catalogue P N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem normal_total
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPreprimitive P (Fin 12)]
    (A B : Subgroup P) (hA : A.Normal) (hB : B.Normal) : A≤B ∨ B≤A := by
  obtain ⟨U,c,hc,hp,⟨D⟩⟩ := exists_exact_profile socle P
  letI := hp
  let e : P ≃* preE7NonPairAction 12 U := actionConjugacyEquiv c hc
  exact normalSubgroups_total_of_surjective e.symm.toMonoidHom e.symm.surjective
    (catalogue.normal_total D (Or.inr rfl)) A B hA hB

theorem quotientSocle_one
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPreprimitive P (Fin 12)]
    (N : Subgroup P) [N.Normal] : SocleNormalGeneratorBound (P ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total (_root_.SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators.BoundedCatalogueReduced.normal_total socle catalogue P) N

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.PrimitiveTwelveFinalPublishedNormalGenerators

end

