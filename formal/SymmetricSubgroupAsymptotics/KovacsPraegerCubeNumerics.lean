import SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBoundPGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Integer cube budgets avoid multiplying real prime bounds on a shared
support. Every prime `p` satisfies `p^3 <= 3^p`; the original prime-action
degree therefore pays the full abelianization cube. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.KovacsPraegerCubeNumerics

theorem nat_cube_le_three_pow (n : ℕ) (hn : 2 ≤ n) : n ^ 3 ≤ 3 ^ n := by
  have hlarge : ∀ k : ℕ, (k + 3) ^ 3 ≤ 3 ^ (k + 3) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      calc
        (k.succ + 3) ^ 3 ≤ 3 * (k + 3) ^ 3 := by
          have h2 : 0 ≤ k ^ 2 := Nat.zero_le _
          have h3 : 0 ≤ k ^ 3 := Nat.zero_le _
          simp only [Nat.succ_eq_add_one]
          nlinarith
        _ ≤ 3 * 3 ^ (k + 3) := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (k.succ + 3) := by
          rw [show k.succ + 3 = (k + 3) + 1 by omega, pow_succ]
          exact Nat.mul_comm _ _
  by_cases htwo : n = 2
  · subst n
    norm_num
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
    rw [hk]
    simpa only [Nat.add_comm] using hlarge k

theorem pGroup_abelianization_cube_le
    (p : ℕ) [Fact p.Prime]
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup p G) :
    Nat.card (Abelianization G) ^ 3 ≤ 3 ^ Nat.card X := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h := PermutationAbelianQuotientOrderBound.pGroup_abelianization_card_le p G X hG
  calc
    Nat.card (Abelianization G) ^ 3 ≤ (p ^ (Nat.card X / p)) ^ 3 :=
      Nat.pow_le_pow_left h 3
    _ = (p ^ 3) ^ (Nat.card X / p) := by
      simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (3 ^ p) ^ (Nat.card X / p) :=
      Nat.pow_le_pow_left (nat_cube_le_three_pow p hp) _
    _ = 3 ^ (p * (Nat.card X / p)) := (pow_mul _ _ _).symm
    _ ≤ 3 ^ Nat.card X := Nat.pow_le_pow_right (by decide) (Nat.mul_div_le _ _)

theorem real_card_bound_of_cube (a n : ℕ) (h : a ^ 3 ≤ 3 ^ n) :
    (a : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 3) := by
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
  calc
    (a : ℝ) ^ 3 ≤ (3 : ℝ) ^ n := by exact_mod_cast h
    _ = ((3 : ℝ) ^ ((n : ℝ) / 3)) ^ 3 := by
      rw [← Real.rpow_natCast (3 : ℝ) n,
        ← Real.rpow_natCast ((3 : ℝ) ^ ((n : ℝ) / 3)) 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring

end SymmetricSubgroupAsymptotics.KovacsPraegerCubeNumerics
