import SymmetricSubgroupAsymptotics.CFSGTypeARankOneEvenClassCube
import SymmetricSubgroupAsymptotics.PrimitiveSocleModelClassCubeSquareClassBound

/-! Every original even-field rank-one simple component from q=8 is
paid uniformly in both raw degree forms and every factor count. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_one_even_capacity
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hp : q.prime=2) (hq : 8 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.A 1 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  refine D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.A 1 q) e q.order
    (by omega) ?_ (CFSGTypeARankOneEvenClassCube.component_class_cube q hp hq)
    (CFSGTypeARankOneSmallPrimeClassCube.field_square_le_order q (by omega)) H hH
  intro K hK
  simpa only [q.card_field] using CFSGPSLTwoEvenPermutationDegree.field_card_le_proper_index
    (F:=q.Field) (by simpa only [ringChar.eq q.Field q.prime] using hp) K hK

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
