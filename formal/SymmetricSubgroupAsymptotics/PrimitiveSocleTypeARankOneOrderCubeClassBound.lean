import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeAUnitaryOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneComponentOrderCube

/-! Original rank-one A components of field size at least128 pay the
class cube at every degree and factor count. Together with the checked
higher-rank parameter tails this leaves an explicit FINITE field/rank
frontier for the complete A family, retaining each actual model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_typeA_rank_one_capacity
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 128 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.A 1 q) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  refine D.subgroup_class_cube_le_of_component_order_cube ((q.order + 1) / 2) ?_ ?_ ?_ ?_ H
  · omega
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hf : q.order ≤ 2 * (K.map e.toMonoidHom).index := by
      simpa only [q.card_field] using
        CFSGPSLTwoGeometry.field_card_le_twice_proper_index (F := q.Field)
          (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
    rw [hi] at hf
    omega
  · rw [Nat.card_congr e.toEquiv, outer_card_congr e]
    exact CFSGTypeARankOneComponentOrderCube.component_order_cube q hq
  · rw [Nat.card_congr e.toEquiv]
    exact CFSGTypeARankOneComponentOrderCube.order_ge_1024 q hq

theorem NonaffineData.subgroup_class_cube_or_typeA_finite_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A r q) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) ∨
      (r = 1 ∧ q.order ≤ 127) ∨ (r = 2 ∧ q.order ≤ 6) ∨ (r = 3 ∧ q.order ≤ 3) ∨
        (4 ≤ r ∧ r ≤ 6 ∧ q.order = 2) := by
  by_cases hone : r = 1
  · subst r
    by_cases hq : 128 ≤ q.order
    · exact Or.inl (D.subgroup_class_cube_le_of_typeA_rank_one_capacity q hq e H)
    · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
  · rcases D.subgroup_class_cube_or_typeA_small_parameters r hr q e H with hc | hp
    · exact Or.inl hc
    · exact Or.inr (Or.inr (by omega))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
