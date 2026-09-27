import SymmetricSubgroupAsymptotics.BinaryConjugacyClassTable8
import SymmetricSubgroupAsymptotics.BinaryActionCoverage8
import SymmetricSubgroupAsymptotics.BinarySmallConjugacyClassBase

/-! The binary permutation class bound with its actual finite base installed.
Original-point degree-eight coverage supplies the remaining finite input;
the checked block/kernel induction then treats every finite faithful binary
action. No class-count assumption remains in the final theorem. This does
not assert the separate 38/25 bound for arbitrary nilpotent groups.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPermutationClassBound

/-- Complete original-action coverage turns the literal 26-row table into
the degree-eight transitive class bound. -/
theorem degree_eight : TransitiveBinaryClassBound 8 25 := by
  intro P hP ht
  letI : MulAction.IsPretransitive P (Fin 8) := ht
  have htrans : PermutationSubgroupTransitive P := by
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P x y
    exact ⟨g, g.property, hg⟩
  exact conjugacyClass_card_le_of_actionRegistryCovered
    BinaryActionRegistry8.actions 25 BinaryConjugacyClassTable8.action_class_card_le
    P (BinaryActionRegistry8.complete P hP htrans)

/-- All binary subgroups of degree at most eight, including intransitive,
empty and singleton actions, satisfy the actual fourth-power finite base. -/
theorem finite_base : BinaryEightPointClassBase :=
  BinarySmallConjugacyClassBase.eightPointClassBase_of_degree_eight degree_eight

/-- The complete integer form of the `5^(2/7)` binary class bound, with
no supplied class-count or finite-base premise. -/
theorem class_card_pow_seven_le
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup 2 G) :
    Nat.card (ConjClasses G) ^ 7 ≤ 5 ^ (2 * Nat.card X) :=
  permutationTwoGroup_conjugacyClass_pow_seven_le finite_base G X hG

theorem literal_class_card_pow_seven_le
    (X : Type) [Finite X] (P : Subgroup (Equiv.Perm X)) (hP : IsPGroup 2 P) :
    Nat.card (ConjClasses P) ^ 7 ≤ 5 ^ (2 * Nat.card X) :=
  class_card_pow_seven_le P X hP

end SymmetricSubgroupAsymptotics.BinaryPermutationClassBound

end
