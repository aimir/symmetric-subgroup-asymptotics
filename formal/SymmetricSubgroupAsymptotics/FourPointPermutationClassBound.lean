import SymmetricSubgroupAsymptotics.FourPointClassRepresentativeCovers
import SymmetricSubgroupAsymptotics.TransitiveFourBinaryOrAlternating
import SymmetricSubgroupAsymptotics.BinaryPermutationClassFourthBound
import SymmetricSubgroupAsymptotics.GaronziMarotiIntransitiveReduction

/-! Every subgroup of the original four-point permutation group has at
most five classes. The transitive case is binary or literally A4/S4;
the intransitive case uses the original invariant-set kernel and image.
There is no enumeration of subgroups, and no subgroup class monotonicity.
The arbitrary-carrier consumer covers EVERY original faithful action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPointPermutationClassBound
open FourPointClassRepresentativeCovers GaronziMarotiIntransitiveReduction

theorem subgroup_class_card_le_five (H : Subgroup (Equiv.Perm (Fin 4))) :
    Nat.card (ConjClasses H) ≤ 5 := by
  by_cases ht : MulAction.IsPretransitive H (Fin 4)
  · rcases TransitiveFourBinaryOrAlternating.binary_or_alternating H ht.exists_smul_eq with
      hbinary | hA
    · have hc := BinaryPermutationClassFourthBound.class_card_pow_four_le H (Fin 4) hbinary
      rw [Nat.card_fin] at hc
      exact (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp hc
    · rcases AlternatingTopImageNormalGenerators.above_alternating H hA with hH | hH
      · subst H
        exact alternating_class_card_le_four.trans (by decide)
      · subst H
        rw [conjugacyClass_card_congr (Subgroup.topEquiv :
          (⊤ : Subgroup (Equiv.Perm (Fin 4))) ≃* Equiv.Perm (Fin 4))]
        exact symmetric_class_card_le_five
  · have hc := intransitive_step (G := H) (X := Fin 4) ht
      (by simp only [Nat.card_fin]; decide)
      (fun m hm h4 _L => False.elim (by rw [Nat.card_fin] at hm; omega))
    have hcube : Nat.card (ConjClasses H)^3 ≤ 5^3 := by
      simpa only [Nat.card_fin, show 4-1=3 by decide] using hc
    exact (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp hcube

theorem faithful_action_class_card_le_five
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hdegree : Nat.card X = 4) :
    Nat.card (ConjClasses G) ≤ 5 := by
  have hbound : ∀ L : Subgroup (Equiv.Perm (Fin (Nat.card X))),
      Nat.card (ConjClasses L)^3 ≤ 5^3 := by
    rw [hdegree]
    intro L
    exact Nat.pow_le_pow_left (subgroup_class_card_le_five L) 3
  have hc := class_cube_le_of_finite_permutation_bound G X _ hbound
  exact (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp hc

theorem faithful_action_class_cube_le_garonziMaroti
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hdegree : Nat.card X = 4) :
    Nat.card (ConjClasses G)^3 ≤ 5^(Nat.card X-1) := by
  have hc := Nat.pow_le_pow_left (faithful_action_class_card_le_five G X hdegree) 3
  simpa only [hdegree, show 4-1=3 by decide] using hc

end SymmetricSubgroupAsymptotics.FourPointPermutationClassBound
