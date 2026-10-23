import SymmetricSubgroupAsymptotics.AffineClassThreeDegreeResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThirtyTwoClassBound

/-! For genuine primitive affine actions, only degrees eight and sixteen
remain in the all-subgroup class-count residual. The degree-32 argument
uses actual elementary translations supplied by primitivity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineClassTwoDegreeResidual

def ResidualDegree (n : ℕ) : Prop := n=8 ∨ n=16

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_cube_or_residual (hprimitive : MulAction.IsPreprimitive G X)
    (x : X) (hn : 4 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨ ResidualDegree (Nat.card X) := by
  rcases AffineClassThreeDegreeResidual.subgroup_class_cube_or_residual P x hn H with h | h
  · exact Or.inl h
  rcases h with h8 | h16 | h32
  · exact Or.inr (Or.inl h8)
  · exact Or.inr (Or.inr h16)
  · exact Or.inl
      (PrimitiveAffineDegreeThirtyTwoClassBound.subgroup_class_cube_le_garonziMaroti
        P hprimitive x h32 H)

end SymmetricSubgroupAsymptotics.PrimitiveAffineClassTwoDegreeResidual
