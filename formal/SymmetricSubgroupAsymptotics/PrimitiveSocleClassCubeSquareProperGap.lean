import SymmetricSubgroupAsymptotics.PrimitiveSocleProperSubnormalClassGap
import SymmetricSubgroupAsymptotics.ComponentOrderCubeWreathExtraGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleModelClassCubeSquareClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleMinimumDegree

/-! The existing exact subnormal CLASS product, rather than simple
group order, pays the proper-subnormal extra exponent. The actual full
socle intersection and quotient image are already handled by the checked
semisimple extension theorem. A square capacity covers the power form
without a large-simple-order assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_class_cube_square
    (D : NonaffineData G X) (b : ℕ) (hb : 3 ≤ b)
    (hindex : ∀ K : Subgroup D.Simple, K ≠ ⊤ → b ≤ K.index)
    (hbase : (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple))^3 ≤ 5^(b-1))
    (hsquare : b^2 ≤ Nat.card D.Simple)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hn := D.degree_lower_of_proper_index_lower b hindex
  by_cases hone : D.factorCount=1
  · exact D.proper_subnormal_class_cube_le_of_factor_one hone (by omega)
      (hbase.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hn 1))) H hH hne
  have htwo : 2 ≤ D.factorCount := by have hp := D.factorCount_pos; omega
  have hc := D.subnormal_class_card_le_outer_wreath H hH
  have hw := ComponentOrderCubeWreathExtraGap.wreath_order_cube_le
    (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple)) b D.factorCount hb htwo hbase
  have hpower : b^D.factorCount ≤ Nat.card X := by
    rcases D.indexForm with ⟨K, hK, hdegree⟩ | ⟨a, hka, hdegree⟩
    · exact (Nat.pow_le_pow_left (hindex K hK) D.factorCount).trans_eq hdegree.symm
    · rw [hdegree]
      calc
        b^D.factorCount ≤ b^(2*a) := Nat.pow_le_pow_right (by omega) hka
        _ = (b^2)^a := pow_mul b 2 a
        _ ≤ (Nat.card D.Simple)^a := Nat.pow_le_pow_left hsquare a
  exact (Nat.pow_le_pow_left hc 3).trans (hw.trans
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hpower 2)))

theorem NonaffineData.proper_subnormal_class_cube_le_of_model_square_capacity
    (D : NonaffineData G X) (S : Type) [Group S] [Finite S]
    (e : D.Simple ≃* S) (b : ℕ) (hb : 3 ≤ b)
    (hindex : ∀ K : Subgroup S, K ≠ ⊤ → b ≤ K.index)
    (hbase : (Nat.card (ConjClasses S)*Nat.card (Outer S))^3 ≤ 5^(b-1))
    (hsquare : b^2 ≤ Nat.card S)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  apply D.proper_subnormal_class_cube_le_of_class_cube_square b hb _ _ _ H hH hne
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hh := hindex (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
    rwa [hi] at hh
  · have hc : Nat.card (ConjClasses D.Simple) ≤ Nat.card (ConjClasses S) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    rw [outer_card_congr e]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hc) 3).trans hbase
  · rwa [Nat.card_congr e.toEquiv]

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
