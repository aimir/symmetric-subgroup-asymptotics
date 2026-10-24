import SymmetricSubgroupAsymptotics.SimpleOrderThreeSixty
import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentClassCubeSquareClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingAllDegreesClassBound

/-! A shared order-360 primitive consumer uses a genuine index gap.
An index-six subgroup supplies an actual A6 equivalence; if none exists,
every proper index is at least eight, and the same class/outer budget
pays both raw degree forms. No exceptional model isomorphism is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

theorem NonaffineData.subnormal_class_cube_le_of_order_three_sixty
    (D : NonaffineData G X) (hcard : Nat.card D.Simple=360)
    (hclasses : Nat.card (ConjClasses D.Simple) ≤ 7)
    (houter : Nat.card (Outer D.Simple) ≤ 4)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  by_cases hsix : ∃K:Subgroup D.Simple,K≠⊤ ∧ K.index=6
  · obtain ⟨K,hK,hindex⟩ := hsix
    let e := SimpleOrderThreeSixty.equivAlternatingSixOfIndexSix hcard K hK hindex
    exact D.subnormal_class_cube_le_of_alternating_all_degrees 6 (by decide) e H hH
  · refine D.subnormal_class_cube_le_of_component_class_cube_square 8 (by decide) ?_ ?_ ?_ H hH
    · intro K hK
      have hlo := SimpleOrderThreeSixty.proper_index_ge_six hcard K hK
      have hne7 := SimpleOrderThreeSixty.proper_index_ne_seven hcard K
      have hne6 : K.index≠6 := by intro h; exact hsix ⟨K,hK,h⟩
      omega
    · exact (Nat.pow_le_pow_left (Nat.mul_le_mul hclasses houter) 3).trans
        (by decide : (7*4)^3 ≤ 5^(8-1))
    · rw [hcard]
      decide

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
