import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators

namespace DirectConsumers

open Non2UnipotentPrefixFiniteMenu

open PrimitiveSixExactProfileNormalGenerators

theorem normal_generating_singletons
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 1 → P, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  exact PrimitiveDegreeSixActualNormalConsumers.normal_generating_singletons catalogue N hN

theorem normalGen_le_one
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)]
    (N : Subgroup P) [N.Normal] : MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨x,hx⟩ := _root_.SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators.DirectConsumers.normal_generating_singletons socle catalogue P N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem five_dvd_card
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    5 ∣ Nat.card P := by
  exact primitive_degreeSix_five_dvd_card_without_catalogue
    (G := P) (X := Fin 6) (by simp)

theorem exists_order_five
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPreprimitive P (Fin 6)] :
    ∃ g : P, orderOf g = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card' 5 (_root_.SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators.DirectConsumers.five_dvd_card socle catalogue P)

end DirectConsumers

end SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators

end

