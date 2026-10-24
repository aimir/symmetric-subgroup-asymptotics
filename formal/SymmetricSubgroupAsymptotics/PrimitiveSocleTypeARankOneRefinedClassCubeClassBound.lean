import SymmetricSubgroupAsymptotics.PrimitiveSocleModelClassCubeSquareClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneSmallPrimeClassCube
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankOneSharpClassCubeClassBound

/-! Additional same-model rank-one consumers share one square-capacity
transport theorem. No finite primitive-action catalogue is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_one_odd_capacity
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 13 ≤ q.order)
    (hp : q.prime≠2) (e : D.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  refine D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.A 1 q) e
    ((q.order+1)/2) (by omega) ?_
    (CFSGTypeARankOneOddClassCube.component_class_cube q hq hp)
    (CFSGTypeARankOneOddClassCube.half_field_square_le_order q (by omega)) H hH
  intro K hK
  have hf : q.order ≤ 2*K.index := by
    simpa only [q.card_field] using CFSGPSLTwoGeometry.field_card_le_twice_proper_index
      (F:=q.Field) K hK
  omega

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_one_small_prime_capacity
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hprime : q.order.Prime)
    (hlo : 7 ≤ q.order) (hhi : q.order ≤ 11) (hmod : q.order%4=3)
    (e : D.Simple ≃* CFSG.Models.A 1 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  refine D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.A 1 q) e q.order
    (by omega) ?_ (CFSGTypeARankOneSmallPrimeClassCube.component_class_cube q hprime hlo hhi)
    (CFSGTypeARankOneSmallPrimeClassCube.field_square_le_order q (by omega)) H hH
  intro K hK
  simpa only [q.card_field] using
    CFSGPSLTwoThreeModFourPermutationDegree.field_card_le_proper_index
      (F:=q.Field) (by simpa only [q.card_field] using hmod) K hK

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
