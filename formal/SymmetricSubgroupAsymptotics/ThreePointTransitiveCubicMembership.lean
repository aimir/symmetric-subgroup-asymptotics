import SymmetricSubgroupAsymptotics.TwoBinaryThreePermutationCoordinates
import SymmetricSubgroupAsymptotics.ProductBlockFrameTransitiveTop

/-! The cubic used in the physical two-head coordinates is an element
of the actual transitive three-point top, not an extra structural input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ThreePointTransitiveCubicMembership

private theorem rotation_word : ∀ a b : Equiv.Perm (Fin 3), a 0=1 → b 0=2 →
    a=OddMarkerTernaryChart.rotation ∨ a⁻¹=OddMarkerTernaryChart.rotation ∨
    b=OddMarkerTernaryChart.rotation ∨ b⁻¹=OddMarkerTernaryChart.rotation ∨
    a*b=OddMarkerTernaryChart.rotation ∨ b*a=OddMarkerTernaryChart.rotation := by
  decide +kernel

theorem rotation_mem (T : Subgroup (Equiv.Perm (Fin 3)))
    (ht : ∀ i j : Fin 3,∃ g : T,(g : Equiv.Perm (Fin 3)) i=j) :
    OddMarkerTernaryChart.rotation∈T := by
  obtain ⟨a,ha⟩ := ht 0 1
  obtain ⟨b,hb⟩ := ht 0 2
  rcases rotation_word a.val b.val ha hb with h | h | h | h | h | h
  · exact h ▸ a.property
  · exact h ▸ T.inv_mem a.property
  · exact h ▸ b.property
  · exact h ▸ T.inv_mem b.property
  · exact h ▸ T.mul_mem a.property b.property
  · exact h ▸ T.mul_mem b.property a.property

theorem frame_rotation_mem {X A : Type} {U : Subgroup (Equiv.Perm X)}
    (C : ProductBlockFrame U (Fin 3) A) [Nonempty A]
    (htrans : ∀ x y : X,∃ u : U,(u : Equiv.Perm X) x=y) :
    OddMarkerTernaryChart.rotation∈C.top.range :=
  rotation_mem C.top.range (C.top_range_transitive htrans)

end SymmetricSubgroupAsymptotics.ThreePointTransitiveCubicMembership
