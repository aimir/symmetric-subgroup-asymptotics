import SymmetricSubgroupAsymptotics.BinaryPermutationClassFourthBound
import SymmetricSubgroupAsymptotics.TernaryPermutationClassFourthBound
import SymmetricSubgroupAsymptotics.NilpotentConjugacyClassPrimeReduction
import SymmetricSubgroupAsymptotics.BinaryCharacterEnvelope

/-! The nilpotent conjugacy-class input is a theorem. Prime-power actions
satisfy an actual fourth-power bound; coprime original-support compression
then gives the precise published1.52 interface without overlapping supports. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NilpotentConjugacyClassProof

/-- Each actual prime action pays the full class count to the fourth power. -/
theorem prime_class_card_pow_four_le (p : ℕ) [Fact p.Prime]
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup p G) :
    Nat.card (ConjClasses G)^4 ≤ 5^Nat.card X := by
  by_cases htwo : p=2
  · subst p
    exact BinaryPermutationClassFourthBound.class_card_pow_four_le G X hG
  by_cases hthree : p=3
  · subst p
    exact TernaryPermutationClassFourthBound.class_card_pow_four_le G X hG
  have hp : 5 ≤ p := by
    have hprime : p.Prime := Fact.out
    by_contra h
    have hsmall : p ≤ 4 := by omega
    interval_cases p <;> norm_num at *
  exact LargePrimePermutationClassFourthBound.class_card_pow_four_le p hp G X hG

private theorem real_bound_of_fourth (a n : ℕ) (h : a^4 ≤ 5^n) :
    (a : ℝ) ≤ (38/25 : ℝ)^n := by
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
  calc
    (a : ℝ)^4 ≤ (5 : ℝ)^n := by exact_mod_cast h
    _ ≤ ((38/25 : ℝ)^4)^n := pow_le_pow_left₀ (by norm_num)
      (by norm_num : (5 : ℝ) ≤ (38/25 : ℝ)^4) n
    _ = ((38/25 : ℝ)^n)^4 := by simp only [←pow_mul,Nat.mul_comm]

/-- Every finite nilpotent group with its actual faithful permutation
action satisfies the precise1.52 bound. -/
theorem class_card_le (G X : Type) [Group G] [Finite G]
    [Group.IsNilpotent G] [Finite X] [MulAction G X] [FaithfulSMul G X] :
    (Nat.card (ConjClasses G) : ℝ) ≤ (38/25 : ℝ)^Nat.card X := by
  apply NilpotentConjugacyClassPrimeReduction.class_bound_of_prime_bounds
    (38/25 : ℝ) (by norm_num) ?_ G X
  intro p _ P Y _ _ _ _ _ hP
  exact real_bound_of_fourth _ _ (prime_class_card_pow_four_le p P Y hP)

/-- Exact formerly retained Maróti field, with no literature premise. -/
theorem nilpotentConjugacyClassInput : NilpotentConjugacyClassInput := by
  intro b P hP
  letI : Group.IsNilpotent P := hP
  simpa only [Nat.card_fin] using class_card_le P (Fin b)

end SymmetricSubgroupAsymptotics.NilpotentConjugacyClassProof
