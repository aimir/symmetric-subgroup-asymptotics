import SymmetricSubgroupAsymptotics.OriginalMinimalBlockAffineTopClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockPrimeAffineTopClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockLowDimensionAffineTopClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineNineTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentyFiveTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixtyFourTopSmallFibreClassBound

/-! One native predicate assembles the proved affine-top ranges.
Every branch retains a literal regular normal prime-power subgroup;
none is a class-bound or numerical-capacity premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

def HasSupportedAffineTop : Prop :=
  ∃ P : PrimitiveAffineProfile D.Top D.Points,
    128≤Nat.card D.Points ∨
      ((Nat.card D.Points).Prime ∧ 5 ≤ Nat.card D.Points) ∨
      ((49 ≤ Nat.card D.Points ∧ Nat.log P.p (Nat.card D.Points) ≤ 3) ∨
        (64 ≤ Nat.card D.Points ∧ Nat.log P.p (Nat.card D.Points) ≤ 4)) ∨
      (MulAction.IsPreprimitive D.Top D.Points ∧
        ((Nat.card D.Points=8 ∨ Nat.card D.Points=16 ∨ Nat.card D.Points=32) ∨
          Nat.card D.Points=9 ∨ Nat.card D.Points=25 ∨ Nat.card D.Points=64))

theorem subnormal_class_cube_le_of_supported_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (h : D.HasSupportedAffineTop) (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  rcases h with ⟨P,hn|⟨hp,hn⟩|hd|⟨hprimitive,hdegree⟩⟩
  · exact D.subnormal_class_cube_le_of_large_affine_top hc hn P H hH
  · exact D.subnormal_class_cube_le_of_prime_affine_top hc hp hn P H hH
  · exact D.subnormal_class_cube_le_of_low_dimension_affine_top hc P hd H hH
  · rcases hdegree with hbinary | h9 | h25 | h64
    · exact D.subnormal_class_cube_le_of_primitive_binary_affine_top
        hc P hprimitive hbinary H hH
    · exact D.subnormal_class_cube_le_of_primitive_nine_affine_top
        hc P hprimitive h9 H hH
    · exact D.subnormal_class_cube_le_of_primitive_twentyFive_affine_top
        hc P hprimitive h25 H hH
    · exact D.subnormal_class_cube_le_of_primitive_sixtyFour_affine_top
        hc P hprimitive h64 H hH

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
