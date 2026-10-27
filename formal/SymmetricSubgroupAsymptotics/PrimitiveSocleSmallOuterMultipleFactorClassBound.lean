import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.AlternatingSocleProductOrderNumerics
import SymmetricSubgroupAsymptotics.PerfectSmallPermutationEmbedding

/-! A finite-head structural simplification. The factorial-product numerics
are group-independent: any actual simple socle with outer order at most two
pays every proper-index degree form with at least two factors. No model class
census, model order, action enumeration or minimum-index table is used.
The outer bound is an explicit local group-theoretic hypothesis, not installed
as a new global GM assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_outer_two_index_form
    (D : NonaffineData G X) (ho : Nat.card (Outer D.Simple) ≤ 2)
    (hk : 2 ≤ D.factorCount) (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X=K.index^D.factorCount) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hm : 5 ≤ K.index := nonabelianSimple_proper_index_five_le
    (fun hc => D.noncommutative (isMulCommutative_iff.mpr hc)) K hK
  have hs : Nat.card D.Simple ≤ K.index.factorial := simple_card_le_index_factorial K hK
  have hso : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ 2*K.index.factorial := by
    have h := Nat.mul_le_mul hs ho
    simpa only [Nat.mul_comm] using h
  have hc : Nat.card (ConjClasses H) ≤
      (2*K.index.factorial)^D.factorCount*D.factorCount.factorial := by
    apply (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans
    exact H.card_le_card_group.trans (D.card_le_simple_outer_wreath.trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hso _)))
  have hn := AlternatingSocleProductOrderNumerics.factorial_product_cube
    K.index D.factorCount hm hk
  rw [hdegree]
  exact (Nat.pow_le_pow_left hc 3).trans hn

theorem NonaffineData.subgroup_class_cube_le_of_outer_two_multiple_factors
    (D : NonaffineData G X) (ho : Nat.card (Outer D.Simple) ≤ 2)
    (hk : 2 ≤ D.factorCount) (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_outer_two_index_form ho hk K hK hdegree H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
