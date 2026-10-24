import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentClassCubeClassBound

/-! A proper-index square budget pays both raw degree forms directly.
The same component class cube and full factorial are used, without a
large-socle threshold or an all-subgroup class monotonicity assertion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_component_class_cube_square
    (D : NonaffineData G X) (b : ℕ) (hb : 3 ≤ b)
    (hindex : ∀ K : Subgroup D.Simple, K≠⊤ → b ≤ K.index)
    (hbase : (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple))^3 ≤ 5^(b-1))
    (hsquare : b^2 ≤ Nat.card D.Simple) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subnormal_class_cube_le_of_component_class_cube_index b hb hbase
      K (hindex K hK) hdegree H hH
  · have hc := D.subnormal_class_card_le_outer_wreath H hH
    have hw := ComponentOrderCubeWreathNumerics.wreath_order_cube_le
      (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple)) b D.factorCount
      hb D.factorCount_pos hbase
    have hn : b^D.factorCount ≤ Nat.card X := by
      rw [hdegree]
      calc
        b^D.factorCount ≤ b^(2*a) := Nat.pow_le_pow_right (by omega) hka
        _ = (b^2)^a := pow_mul b 2 a
        _ ≤ (Nat.card D.Simple)^a := Nat.pow_le_pow_left hsquare a
    exact (Nat.pow_le_pow_left hc 3).trans (hw.trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hn 1)))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
