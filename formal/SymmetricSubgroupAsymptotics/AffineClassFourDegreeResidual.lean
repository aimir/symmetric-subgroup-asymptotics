import SymmetricSubgroupAsymptotics.AffineClassFiveDegreeResidual
import SymmetricSubgroupAsymptotics.FourPointPermutationClassBound

/-! The all-subgroup affine class-count residual has only four degrees.
Degree four is discharged for every faithful action, using the original
binary/alternating dichotomy and the actual A4/S4 conjugacy covers. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AffineClassFourDegreeResidual

def ResidualDegree (n : ℕ) : Prop := n=8 ∨ n=9 ∨ n=16 ∨ n=32

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_cube_or_residual (x : X) (hn : 4 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨ ResidualDegree (Nat.card X) := by
  rcases AffineClassFiveDegreeResidual.subgroup_class_cube_or_residual P x hn H with h | h
  · exact Or.inl h
  rcases h with h4 | hrest
  · exact Or.inl
      (FourPointPermutationClassBound.faithful_action_class_cube_le_garonziMaroti H X h4)
  · exact Or.inr hrest

end SymmetricSubgroupAsymptotics.AffineClassFourDegreeResidual
