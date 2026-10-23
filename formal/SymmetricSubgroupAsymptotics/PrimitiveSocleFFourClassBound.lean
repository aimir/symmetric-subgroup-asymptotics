import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGFFourE6PermutationDegree
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The original F4 component satisfies the large primitive class cube bound.
This applies to every subgroup and both raw socle degree forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGFFourOriginalOrderUpper CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.fFour_simple_order_outer_budget
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.F4 q)
    (K : Subgroup D.Simple) (hK : K ≠ ⊤) :
    Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ K.index ^ 66 := by
  letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.F4 q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hproper : K.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hi := CFSGFFourE6PermutationDegree.field_card_le_proper_index
    q.Field q.prime (K.map e.toMonoidHom) hproper
  have hindex : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
  rw [q.card_field, hindex] at hi
  rw [Nat.card_congr e.toEquiv, outer_card_congr e]
  exact (typeFFour_order_mul_outer_le q hn).trans (Nat.pow_le_pow_left hi 66)

theorem NonaffineData.subgroup_class_cube_le_of_fFour
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.F4 q)
    (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  rcases D.indexForm with ⟨K, hK, hdegree⟩ | ⟨a, hka, hdegree⟩
  · exact D.subgroup_class_cube_le_of_bounded_component K hK hdegree
      (D.fFour_simple_order_outer_budget q e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
