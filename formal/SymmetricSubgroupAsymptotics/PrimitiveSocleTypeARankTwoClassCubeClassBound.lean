import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoClassCube
import SymmetricSubgroupAsymptotics.PrimitiveSocleModelClassCubeSquareClassBound

/-! The rank-two A class-capacity theorem on the original primitive data,
retaining its actual model equivalence, every socle factor and both raw
degree forms. Only the two-element field remains outside this consumer.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X:Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_two
    (D:NonaffineData G X) (q:CFSG.PrimePower) (hq:3≤q.order)
    (e:D.Simple≃*CFSG.Models.A 2 q) (H:Subgroup G) (hH:H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 2 q) := e.symm.isSimpleGroup
  exact D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.A 2 q) e
    (q.order^2) ((by decide : 3≤3^2).trans (Nat.pow_le_pow_left hq 2))
    (CFSGTypeARankTwoClassCube.proper_index_lower q)
    (CFSGTypeARankTwoClassCube.component_class_cube q hq)
    (CFSGTypeARankTwoClassCube.field_fourth_le_card q) H hH

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
