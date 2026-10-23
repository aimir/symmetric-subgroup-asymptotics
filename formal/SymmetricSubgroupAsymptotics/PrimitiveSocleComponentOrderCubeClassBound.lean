import SymmetricSubgroupAsymptotics.ComponentOrderCubeWreathNumerics
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound

/-! Concrete model ORDER cubes, once numerically checked at a literal
proper-index lower bound, pay every factor count at every index-form
degree. The original full socle, quotient image and k! are all retained.
The power form uses the already proved large-degree theorem only when
the actual simple component is itself large enough. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_component_order_cube_index
    (D : NonaffineData G X) (b : ℕ) (hb : 3 ≤ b)
    (hbase : (Nat.card D.Simple * Nat.card (Outer D.Simple)) ^ 3 ≤ 5 ^ (b - 1))
    (K : Subgroup D.Simple) (hindex : b ≤ K.index)
    (hdegree : Nat.card X = K.index ^ D.factorCount) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  have hc : Nat.card (ConjClasses H) ≤
      (Nat.card D.Simple * Nat.card (Outer D.Simple)) ^ D.factorCount *
        D.factorCount.factorial :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans
      (H.card_le_card_group.trans D.card_le_simple_outer_wreath)
  have hw := ComponentOrderCubeWreathNumerics.wreath_order_cube_le
    (Nat.card D.Simple * Nat.card (Outer D.Simple)) b D.factorCount hb D.factorCount_pos hbase
  exact (Nat.pow_le_pow_left hc 3).trans (hw.trans
    (Nat.pow_le_pow_right (by decide)
      (Nat.sub_le_sub_right ((Nat.pow_le_pow_left hindex D.factorCount).trans_eq hdegree.symm) 1)))

theorem NonaffineData.subgroup_class_cube_le_of_component_order_cube
    (D : NonaffineData G X) (b : ℕ) (hb : 3 ≤ b)
    (hindex : ∀ K : Subgroup D.Simple, K ≠ ⊤ → b ≤ K.index)
    (hbase : (Nat.card D.Simple * Nat.card (Outer D.Simple)) ^ 3 ≤ 5 ^ (b - 1))
    (hlarge : 1024 ≤ Nat.card D.Simple) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  rcases D.indexForm with ⟨K, hK, hdegree⟩ | ⟨a, hka, hdegree⟩
  · exact D.subgroup_class_cube_le_of_component_order_cube_index b hb hbase
      K (hindex K hK) hdegree H
  · have ha : a ≠ 0 := by have hp := D.factorCount_pos; omega
    have hn : 1024 ≤ Nat.card X := by
      rw [hdegree]
      exact hlarge.trans (Nat.le_self_pow ha _)
    exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
