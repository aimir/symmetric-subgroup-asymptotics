import SymmetricSubgroupAsymptotics.SupportedSmallAffineTopProfiles
import SymmetricSubgroupAsymptotics.RegularAffineEightTernaryCoarsening
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockAffineTopClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockPrimeAffineTopClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockLowDimensionAffineTopClassBound
import SymmetricSubgroupAsymptotics.AffineTopRemainingPrimePowerDegrees

/-! Every actual bare regular normal prime-group top of degree at least
five pays the original small-fibre action under strict-smaller GENERAL
permutation IH. Genuine prime-power arithmetic exhausts the source;
no preprimitive, elementary, class-budget or catalogue premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem class_cube_le_of_regular_affine_top_complete
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (P : PrimitiveAffineProfile D.Top D.Points) (hn : 5≤Nat.card D.Points)
    (hSmaller : ∀ m : ℕ, m < (Nat.card Ω) → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)), Nat.card (ConjClasses L)^3≤5^(m-1)) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  by_cases hlarge : 128≤Nat.card D.Points
  · exact D.class_cube_le_of_large_affine_top hc hlarge P
  by_cases hprime : (Nat.card D.Points).Prime
  · exact D.class_cube_le_of_prime_affine_top hc hprime hn P
  by_cases hlow : (49≤Nat.card D.Points ∧ Nat.log P.p (Nat.card D.Points)≤3) ∨
      (64≤Nat.card D.Points ∧ Nat.log P.p (Nat.card D.Points)≤4)
  · exact D.class_cube_le_of_low_dimension_affine_top hc P hlow
  have hdegree := AffineTopRemainingPrimePowerDegrees.degree_of_uncovered_profile
    P hn hlarge hprime hlow
  rcases hdegree with h8|h9|h16|h25|h27|h32|h64
  · rcases hc with htwo|hthree
    · exact D.class_cube_le_of_supported_small_affine_top (Or.inl htwo)
        ⟨P,Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨h8,htwo⟩))))⟩
    · exact D.class_cube_le_of_ternary_eight_affine_top hthree P h8 hSmaller
  · exact D.class_cube_le_of_supported_small_affine_top hc
      ⟨P,Or.inr (Or.inr (Or.inl h9))⟩
  · exact D.class_cube_le_of_supported_small_affine_top hc ⟨P,Or.inl (Or.inl h16)⟩
  · exact D.class_cube_le_of_supported_small_affine_top hc
      ⟨P,Or.inr (Or.inr (Or.inr h25))⟩
  · exact D.class_cube_le_of_supported_small_affine_top hc
      ⟨P,Or.inl (Or.inr (Or.inl h27))⟩
  · exact D.class_cube_le_of_supported_small_affine_top hc
      ⟨P,Or.inl (Or.inr (Or.inr (Or.inl h32)))⟩
  · exact D.class_cube_le_of_supported_small_affine_top hc
      ⟨P,Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h64))))⟩

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
