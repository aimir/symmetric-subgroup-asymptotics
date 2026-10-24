import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentClassCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneClassCube
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankOneSharpClassBound

/-! The proved trace-class budget narrows the actual A1 frontier while
retaining every original subnormal subgroup and both raw degree forms. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_one_class_capacity
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 27 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.A 1 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  refine D.subnormal_class_cube_le_of_component_class_cube ((q.order+1)/2) ?_ ?_ ?_ ?_ H hH
  · omega
  · intro K hK
    have hmap : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hf : q.order ≤ 2*(K.map e.toMonoidHom).index := by
      simpa only [q.card_field] using
        CFSGPSLTwoGeometry.field_card_le_twice_proper_index (F:=q.Field)
          (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [hi] at hf
    omega
  · have hc : Nat.card (ConjClasses D.Simple) ≤
        Nat.card (ConjClasses (CFSG.Models.A 1 q)) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    rw [outer_card_congr e]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hc) 3).trans
      (CFSGTypeARankOneClassCube.component_class_cube q hq)
  · rw [Nat.card_congr e.toEquiv]
    exact CFSGTypeARankOneOrderThreshold.order_ge_1024 q (by omega)

theorem NonaffineData.subnormal_class_cube_or_typeA_class_finite_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A r q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨
      (r=1 ∧ q.order≤26) ∨ (r=2 ∧ q.order≤6) ∨ (r=3 ∧ q.order≤3) ∨
        (4≤r ∧ r≤6 ∧ q.order=2) := by
  by_cases hone : r=1
  · subst r
    by_cases hq : 27 ≤ q.order
    · exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_one_class_capacity q hq e H hH)
    · exact Or.inr (Or.inl ⟨rfl,by omega⟩)
  · rcases D.subgroup_class_cube_or_typeA_small_parameters r hr q e H with hc | hp
    · exact Or.inl hc
    · exact Or.inr (Or.inr (by omega))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
