import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSubnormalClassBound

/-! An actual component CLASS cube pays every socle factor for an
original subnormal subgroup. The intersection with the full socle is
handled through whole simple coordinates, so no class monotonicity for
arbitrary simple subgroups is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_component_class_cube_index
    (D : NonaffineData G X) (b : ℕ) (hb : 3 ≤ b)
    (hbase : (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple))^3 ≤ 5^(b-1))
    (K : Subgroup D.Simple) (hindex : b ≤ K.index)
    (hdegree : Nat.card X=K.index^D.factorCount) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hc := D.subnormal_class_card_le_outer_wreath H hH
  have hw := ComponentOrderCubeWreathNumerics.wreath_order_cube_le
    (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple)) b D.factorCount
    hb D.factorCount_pos hbase
  exact (Nat.pow_le_pow_left hc 3).trans (hw.trans
    (Nat.pow_le_pow_right (by decide)
      (Nat.sub_le_sub_right ((Nat.pow_le_pow_left hindex D.factorCount).trans_eq hdegree.symm) 1)))

theorem NonaffineData.subnormal_class_cube_le_of_component_class_cube
    (D : NonaffineData G X) (b : ℕ) (hb : 3 ≤ b)
    (hindex : ∀ K : Subgroup D.Simple, K≠⊤ → b ≤ K.index)
    (hbase : (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple))^3 ≤ 5^(b-1))
    (hlarge : 1024 ≤ Nat.card D.Simple) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subnormal_class_cube_le_of_component_class_cube_index b hb hbase
      K (hindex K hK) hdegree H hH
  · have ha : a≠0 := by have hp := D.factorCount_pos; omega
    have hn : 1024 ≤ Nat.card X := by
      rw [hdegree]
      exact hlarge.trans (Nat.le_self_pow ha _)
    exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
