import SymmetricSubgroupAsymptotics.AffineClassFourDegreeResidual
import SymmetricSubgroupAsymptotics.AffineDegreeNineSubgroupClassBound

/-! The actual all-subgroup affine class-count residual is reduced to
three binary degrees. Degree nine uses the original regular group and
faithful complement action, including its cyclic regular-group case. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AffineClassThreeDegreeResidual

def ResidualDegree (n : ℕ) : Prop := n=8 ∨ n=16 ∨ n=32

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_cube_or_residual (x : X) (hn : 4 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨ ResidualDegree (Nat.card X) := by
  rcases AffineClassFourDegreeResidual.subgroup_class_cube_or_residual P x hn H with h | h
  · exact Or.inl h
  rcases h with h8 | h9 | h16 | h32
  · exact Or.inr (Or.inl h8)
  · exact Or.inl
      (AffineDegreeNineSubgroupClassBound.subgroup_class_cube_le_garonziMaroti P x h9 H)
  · exact Or.inr (Or.inr (Or.inl h16))
  · exact Or.inr (Or.inr (Or.inr h32))

end SymmetricSubgroupAsymptotics.AffineClassThreeDegreeResidual
