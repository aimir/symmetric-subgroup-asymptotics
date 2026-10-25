import SymmetricSubgroupAsymptotics.PrimitiveSocleClassCubeSquareProperGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankTwoCompleteClassBound

/-! The actual rank-two A packets pay the proper-subnormal extra gap
in every field, every original representation and every socle factor
count. The two-element field uses its proved index-seven/order-168
packet, not an exceptional-isomorphism premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_pslThree_all_fields
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A 2 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 2 q) := e.symm.isSimpleGroup
  by_cases hq : 3 ≤ q.order
  · exact D.proper_subnormal_class_cube_le_of_model_square_capacity
      (CFSG.Models.A 2 q) e (q.order^2)
      ((by decide : 3 ≤ 3^2).trans (Nat.pow_le_pow_left hq 2))
      (CFSGTypeARankTwoClassCube.proper_index_lower q)
      (CFSGTypeARankTwoClassCube.component_class_cube q hq)
      (CFSGTypeARankTwoClassCube.field_fourth_le_card q) H hH hne
  have htwo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hq2 : q.order=2 := by omega
  have he : q.exponent=1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
      (show q.prime^q.exponent=2^1 from hq2)).2
  have hc : Nat.card (ConjClasses (CFSG.Models.A 2 q)) ≤ 8 := by
    simpa only [hq2] using CFSGTypeARankTwoClassCube.class_card_le q
  have ho : Nat.card (Outer (CFSG.Models.A 2 q)) ≤ 2 := by
    simpa only [hq2, he] using
      CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd 2 (by decide) q
  refine D.proper_subnormal_class_cube_le_of_model_square_capacity
    (CFSG.Models.A 2 q) e 7 (by decide)
    (CFSGTypeARankTwoCardTwo.proper_index_ge_seven q hq2) ?_ ?_ H hH hne
  · exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans
      (by decide : (8*2)^3 ≤ 5^(7-1))
  · rw [CFSGTypeARankTwoCardTwo.order_eq_168 q hq2]
    decide

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
