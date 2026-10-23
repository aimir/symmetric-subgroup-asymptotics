import SymmetricSubgroupAsymptotics.PrimitiveAffineClassTwoDegreeResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinarySmallClassBound

/-! The class-count cube bound for every subgroup of every original
faithful primitive affine action of degree at least four. All finite
degree branches and the infinite tail are discharged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineAllSubgroupsClassBound
variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_cube_le_garonziMaroti
    (hprimitive : MulAction.IsPreprimitive G X) (x : X)
    (hn : 4 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases PrimitiveAffineClassTwoDegreeResidual.subgroup_class_cube_or_residual
      P hprimitive x hn H with h | h
  · exact h
  · exact PrimitiveAffineBinarySmallClassBound.subgroup_class_cube_le_garonziMaroti
      P hprimitive x h H

end SymmetricSubgroupAsymptotics.PrimitiveAffineAllSubgroupsClassBound
