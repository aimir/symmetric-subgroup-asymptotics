import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.CFSGGTwoProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The original G2 simple type pays the large primitive class cube for
every subgroup and every socle factor count, using its actual natural
representation and original outer bound. Both raw degree forms are
covered; no project-owned model bound remains a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.gTwo_simple_order_outer_budget
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hsmall : q.order≠2)
    (e : D.Simple ≃* CFSG.Models.G2 q) (K : Subgroup D.Simple) (hK : K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple) ≤ K.index^66 := by
  letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
  have hmap : K.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hb := CFSGGTwoProperIndexOrderBudget.typeGTwo_order_mul_outer_le_proper_index_power
    q hsmall (K.map e.toMonoidHom) hmap
  have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
  rw [hidx] at hb
  rw [Nat.card_congr e.toEquiv, CFSGReduction.outer_card_congr e]
  exact hb

theorem NonaffineData.subgroup_class_cube_le_of_gTwo
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hsmall : q.order≠2)
    (e : D.Simple ≃* CFSG.Models.G2 q) (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_bounded_component K hK hdegree
      (D.gTwo_simple_order_outer_budget q hsmall e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
