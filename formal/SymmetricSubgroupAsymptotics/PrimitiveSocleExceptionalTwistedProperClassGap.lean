import SymmetricSubgroupAsymptotics.PrimitiveSocleModelProperClassCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleLargeIndexOrderProperClassGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedE6CompleteClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourMiddleSuzukiClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourFieldEightClassBound

/-! Existing original-model large-index and middle-Suzuki/selected
prime-index packets pay twisted E6 and every positive ReeF4 parameter.
The original derived/full-centre Ree model is retained; Tits is separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_twistedE6_all_fields
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedE6 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedE6 q) := Finite.of_equiv D.Simple e.toEquiv
  have hindex : ∀ K : Subgroup D.Simple, K ≠ ⊤ → 2048 ≤ K.index := by
    intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGTwistedE6HeisenbergIndex.proper_index_ge_2048 q (K.map e.toMonoidHom) hmap
    have he : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rwa [he] at hi
  have hn := D.degree_lower_of_proper_index_lower 2048 hindex
  exact D.proper_subnormal_class_cube_le_of_large_index_order_budget (by omega)
    (fun K hK => (by decide : 1024 ≤ 2048).trans (hindex K hK))
    (D.twistedE6_simple_order_outer_budget q e) H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_reeFFour_positive_parameters
    (D : NonaffineData G X) (m : ℕ) (hm : 0 < m)
    (e : D.Simple ≃* CFSG.Models.ReeF4 m)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.ReeF4 m) := Finite.of_equiv D.Simple e.toEquiv
  by_cases hone : m=1
  · subst m
    refine D.proper_subnormal_class_cube_le_of_model_order_capacity
      (CFSG.Models.ReeF4 1) e 109 (by decide)
      CFSGReeFFourFieldEightPrimeIndex.proper_index_le ?_ ?_ H hH hne
    · exact (Nat.pow_le_pow_left (Nat.mul_le_mul
        (CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le 1)
        (CFSGReeFFourOriginalOuterBound.outer_card_le 1 (by decide))) 3).trans
          ReeFFourFieldEightClassNumerics.component_order_cube
    · exact ReeFFourFieldEightClassNumerics.order_lower.trans
        (CFSGReeFFourOriginalOrderLower.original_ree_order_ge 1 (by decide))
  · have hm2 : 2 ≤ m := by omega
    have hq : 2 ≤ 2^(2*m+1) :=
      Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (by omega : 1 ≤ 2*m+1)
    refine D.proper_subnormal_class_cube_le_of_model_order_capacity
      (CFSG.Models.ReeF4 m) e (ReeFFourMiddleSuzukiClassNumerics.indexBound m)
      ((by decide : 3 ≤ 248).trans (ReeFFourMiddleSuzukiClassNumerics.index_ge_248 m hm2))
      (CFSGReeFFourMiddleSuzukiIndex.middle_suzuki_le_proper_index m hm) ?_ ?_ H hH hne
    · exact (Nat.pow_le_pow_left (Nat.mul_le_mul
        (CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le m)
        (CFSGReeFFourOriginalOuterBound.outer_card_le m hm)) 3).trans
          (ReeFFourMiddleSuzukiClassNumerics.component_order_cube m hm2)
    · exact (by decide : 1024 ≤ (2 : ℕ)^24).trans
        ((Nat.pow_le_pow_left hq 24).trans
          (CFSGReeFFourOriginalOrderLower.original_ree_order_ge m hm))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
