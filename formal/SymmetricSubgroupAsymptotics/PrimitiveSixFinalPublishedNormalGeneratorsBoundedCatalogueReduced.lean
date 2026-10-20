import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open PrimitiveSixExactProfileNormalGenerators

theorem normal_generating_singletons
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 1 → P, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨U,c,hc,hp,⟨D⟩⟩ := exists_exact_profile socle P
  letI := hp
  let e : P ≃* preE7NonPairAction 6 U := actionConjugacyEquiv c hc
  exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
    (catalogue.normal_generating_singletons D (Or.inl rfl))

theorem normalGen_le_one
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)]
    (N : Subgroup P) [N.Normal] : MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨x,hx⟩ := _root_.SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators.BoundedCatalogueReduced.normal_generating_singletons socle catalogue P N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem five_dvd_card
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    5 ∣ Nat.card P := by
  obtain ⟨U,c,hc,hp,⟨D⟩⟩ := exists_exact_profile socle P
  letI := hp
  let e : P ≃* preE7NonPairAction 6 U := actionConjugacyEquiv c hc
  rw [Nat.card_congr e.toEquiv]
  exact catalogue.six_five_dvd _ D

theorem exists_order_five
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∃ g : P, orderOf g = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card' 5 (_root_.SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators.BoundedCatalogueReduced.five_dvd_card socle catalogue P)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators

end

