import SymmetricSubgroupAsymptotics.OriginalMinimalBlockAffineTopClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockPrimeAffineTopClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockLowDimensionAffineTopClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineNineTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentyFiveTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixtyFourTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineTernaryTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.AffineTopRemainingPrimePowerDegrees

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
      ((MulAction.IsPreprimitive D.Top D.Points ∧
        ((Nat.card D.Points=8 ∨ Nat.card D.Points=16 ∨ Nat.card D.Points=32) ∨
          Nat.card D.Points=9 ∨ Nat.card D.Points=25 ∨ Nat.card D.Points=64 ∨
          Nat.card D.Points=27)) ∨ Nat.card D.Points=9 ∨ Nat.card D.Points=25)

/-- The arithmetic exhaustion and the common native class-budget
consumer pay every actual primitive affine top of degree at least five. -/
theorem hasSupportedAffineTop_of_preprimitive
    (P : PrimitiveAffineProfile D.Top D.Points)
    (hprimitive : MulAction.IsPreprimitive D.Top D.Points)
    (hn : 5 ≤ Nat.card D.Points) : D.HasSupportedAffineTop := by
  by_cases hlarge : 128 ≤ Nat.card D.Points
  · exact ⟨P, Or.inl hlarge⟩
  by_cases hprime : (Nat.card D.Points).Prime
  · exact ⟨P, Or.inr (Or.inl ⟨hprime, hn⟩)⟩
  by_cases hlow : (49 ≤ Nat.card D.Points ∧ Nat.log P.p (Nat.card D.Points) ≤ 3) ∨
      (64 ≤ Nat.card D.Points ∧ Nat.log P.p (Nat.card D.Points) ≤ 4)
  · exact ⟨P, Or.inr (Or.inr (Or.inl hlow))⟩
  have hd := AffineTopRemainingPrimePowerDegrees.degree_of_uncovered_profile
    P hn hlarge hprime hlow
  refine ⟨P, Or.inr (Or.inr (Or.inr (Or.inl ⟨hprimitive, ?_⟩)))⟩
  rcases hd with h8 | h9 | h16 | h25 | h27 | h32 | h64
  · exact Or.inl (Or.inl h8)
  · exact Or.inr (Or.inl h9)
  · exact Or.inl (Or.inr (Or.inl h16))
  · exact Or.inr (Or.inr (Or.inl h25))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h27)))
  · exact Or.inl (Or.inr (Or.inr h32))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h64)))

theorem subnormal_class_cube_le_of_supported_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (h : D.HasSupportedAffineTop) (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  rcases h with ⟨P,hn|⟨hp,hn⟩|hd|⟨hprimitive,hdegree⟩|h9|h25⟩
  · exact D.subnormal_class_cube_le_of_large_affine_top hc hn P H hH
  · exact D.subnormal_class_cube_le_of_prime_affine_top hc hp hn P H hH
  · exact D.subnormal_class_cube_le_of_low_dimension_affine_top hc P hd H hH
  · rcases hdegree with hbinary | h9 | h25 | h64 | h27
    · exact D.subnormal_class_cube_le_of_primitive_binary_affine_top
        hc P hprimitive hbinary H hH
    · exact D.subnormal_class_cube_le_of_primitive_nine_affine_top
        hc P h9 H hH
    · exact D.subnormal_class_cube_le_of_primitive_twentyFive_affine_top
        hc P h25 H hH
    · exact D.subnormal_class_cube_le_of_primitive_sixtyFour_affine_top
        hc P hprimitive h64 H hH
    · exact PrimitiveAffineTernaryTopSmallFibreClassBound.subnormal_class_cube_le_at_original_degree
        D.map D.map_equivariant (Nat.card D.Fibre) hc D.fibre_card_at P hprimitive h27 H hH
  · exact D.subnormal_class_cube_le_of_primitive_nine_affine_top hc P h9 H hH
  · exact D.subnormal_class_cube_le_of_primitive_twentyFive_affine_top hc P h25 H hH

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
