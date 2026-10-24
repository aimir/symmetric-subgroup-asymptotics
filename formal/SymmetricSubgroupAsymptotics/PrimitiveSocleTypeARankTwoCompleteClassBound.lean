import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankTwoClassCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoCardTwo

/-! Complete original rank-two A class capacity, including the two-element
field. Its order-168 coset argument avoids exceptional isomorphism data.
Every original subnormal subgroup and both original degree forms remain.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X:Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_two_card_two
    (D:NonaffineData G X) (q:CFSG.PrimePower) (hq:q.order=2)
    (e:D.Simple≃*CFSG.Models.A 2 q) (H:Subgroup G) (hH:H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 2 q) := e.symm.isSimpleGroup
  have he:q.exponent=1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1:ℕ)≠0)
      (show q.prime^q.exponent=2^1 from hq)).2
  have hc:Nat.card (ConjClasses (CFSG.Models.A 2 q))≤8 := by
    simpa only [hq] using CFSGTypeARankTwoClassCube.class_card_le q
  have ho:Nat.card (Outer (CFSG.Models.A 2 q))≤2 := by
    simpa only [hq,he] using
      CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd 2 (by decide) q
  refine D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.A 2 q) e 7 (by decide)
    (CFSGTypeARankTwoCardTwo.proper_index_ge_seven q hq) ?_ ?_ H hH
  · exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans
      (by decide : (8*2)^3≤5^(7-1))
  · rw [CFSGTypeARankTwoCardTwo.order_eq_168 q hq]
    decide

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_two_all_fields
    (D:NonaffineData G X) (q:CFSG.PrimePower)
    (e:D.Simple≃*CFSG.Models.A 2 q) (H:Subgroup G) (hH:H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  by_cases hq:3≤q.order
  · exact D.subnormal_class_cube_le_of_typeA_rank_two q hq e H hH
  · have htwo:2≤q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact D.subnormal_class_cube_le_of_typeA_rank_two_card_two q (by omega) e H hH

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
