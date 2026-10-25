import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSmallOrbit
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleExchange
import SymmetricSubgroupAsymptotics.SubgroupOrbitFixedMovedSeparation

/-! Two actual sources in the SAME original Model force two disjoint
orbits of size at least twenty-seven. The first small orbit is fixed by
the short central element; the exceptional-image source centralizes that
element pointwise, so its moved orbit is disjoint from the first. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleTwoOrbits
open CFSG.Models.Chevalley
open CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalExceptionalModel
open CFSGGTwoCharacteristicThreeMiddleSource
open CFSGGTwoCharacteristicThreeMiddleLayerCounts
open CFSGGTwoCharacteristicThreeMiddleSmallOrbit
open CFSGGTwoCharacteristicThreeMiddleExchange
variable (K : Type) [Field K] [Finite K] [CharP K 3]

theorem degree_ge_fiftyFour (hcard : Nat.card K = 3)
    {X : Type*} [Finite X] [MulAction (Model CartanMatrix.G₂ K) X]
    (hhigh : ∃ x : X, positiveModel K 5 1 • x ≠ x)
    (hthird : ∃ y : X, positiveModel K 3 1 • y ≠ y) : 54 ≤ Nat.card X := by
  apply SubgroupOrbitFixedMovedSeparation.degree_le_of_two_orbits
    (source K) (exchangedSource K) (positiveModel K 5 1) (positiveModel K 3 1)
    27 27 hhigh hthird
  · intro x hx
    have hm : highestElement K • x ≠ x := by
      change (highestElement K).val • x ≠ x
      rw [highestElement_val]
      exact hx
    exact source_orbit_card_ge_twentySeven K hcard x hm
  · intro x hx hsmall y hy
    have hm : highestElement K • x ≠ x := by
      change (highestElement K).val • x ≠ x
      rw [highestElement_val]
      exact hx
    have he := third_fixes_small_source_orbit K hcard x hm hsmall y hy
    change (thirdElement K).val • y = y at he
    rw [thirdElement_val] at he
    exact he
  · intro y hy
    letI : MulAction (source K) X :=
      MulAction.compHom X (sourceEquivExchanged K).toMonoidHom
    have hh : ((sourceEquivExchanged K) (highestElement K)).val = positiveModel K 3 1 := by
      change exceptionalModelEquiv K (highestElement K).val = positiveModel K 3 1
      rw [highestElement_val,exceptional_highest]
    have hm : highestElement K • y ≠ y := by
      change ((sourceEquivExchanged K) (highestElement K)).val • y ≠ y
      rw [hh]
      exact hy
    have he := source_orbit_card_ge_twentySeven K hcard y hm
    have horbit : MulAction.orbit (source K) y = MulAction.orbit (exchangedSource K) y := by
      ext z
      constructor
      · rintro ⟨g,hg⟩
        exact ⟨sourceEquivExchanged K g,hg⟩
      · rintro ⟨g,hg⟩
        obtain ⟨p,rfl⟩ := (sourceEquivExchanged K).surjective g
        exact ⟨p,hg⟩
    rw [horbit] at he
    exact he
  · intro y hy
    apply SubgroupOrbitFixedMovedSeparation.orbit_motion_of_conjugate_eq_or_inverse
      (exchangedSource K) (positiveModel K 3 1) y hy
    intro g
    left
    have hc := Subgroup.mem_centralizer_singleton_iff.mp
      (exchangedSource_centralizes_third K 1 g.property)
    calc
      g.val⁻¹*positiveModel K 3 1*g.val = g.val⁻¹*(positiveModel K 3 1*g.val) := by group
      _ = g.val⁻¹*(g.val*positiveModel K 3 1) := by rw [←hc]
      _ = positiveModel K 3 1 := by group

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleTwoOrbits
