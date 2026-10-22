import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource

/-! Complete same-sign simple-generator action on original type-A
interval vectors. The interior-node zero is a rational Jacobi/Serre
consequence; no natural-image injectivity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalBrackets
open CFSGTwistedAIntervalJacobi
variable {L : Type} [LieRing L] [Module ℚ L] [LieAlgebra ℚ L]
variable (x : ℕ → L)
  (hfar : ∀ i j, i + 1 < j ∨ j + 1 < i → ⁅x i, x j⁆ = 0)
  (hserre : ∀ i j, i + 1 = j ∨ j + 1 = i → ⁅x i, ⁅x i, x j⁆⁆ = 0)

include hfar hserre

theorem chain_start_square_zero (start n : ℕ) :
    ⁅x start, ⁅x start, chainBracket x (start + 1) n⁆⁆ = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => rw [chainBracket_zero, lie_zero, lie_zero]
  | one => rw [chainBracket_one]; exact hserre start (start + 1) (Or.inl rfl)
  | more n _ _ =>
    rw [chainBracket_step]
    exact outer_serre_inherits (x start) (x (start + 1))
      (chainBracket x (start + 2) (n + 1))
      (lie_chainBracket_far x hfar start (start + 2) (n + 1) (by omega))
      (hserre start (start + 1) (Or.inl rfl))

theorem lie_chainBracket_inside (start n k : ℕ) (hk : start ≤ k ∧ k < start + n) :
    ⁅x k, chainBracket x start n⁆ = 0 := by
  induction n using Nat.twoStepInduction generalizing start k with
  | zero => omega
  | one =>
    have he : k = start := by omega
    subst k
    rw [chainBracket_one, lie_self]
  | more n _ ih =>
    rw [chainBracket_step]
    by_cases h0 : k = start
    · subst k
      exact chain_start_square_zero x hfar hserre start (n + 1)
    by_cases h1 : k = start + 1
    · subst k
      cases n with
      | zero =>
        rw [chainBracket_one]
        have hs : ⁅x start, x (start + 1)⁆ = -⁅x (start + 1), x start⁆ :=
          (lie_skew _ _).symm
        rw [hs, lie_neg, hserre (start + 1) start (Or.inr rfl), neg_zero]
      | succ m =>
        rw [chainBracket_step x (start + 1) m]
        exact middle_bracket_zero (x start) (x (start + 1))
          (chainBracket x (start + 2) (m + 1))
          (lie_chainBracket_far x hfar start (start + 2) (m + 1) (by omega))
          (hserre (start + 1) start (Or.inr rfl))
          (chain_start_square_zero x hfar hserre (start + 1) (m + 1))
    rw [leibniz_lie, hfar k start (by omega), zero_lie, zero_add,
      ih (start + 1) k (by omega), lie_zero]

theorem lie_chainBracket_raising (start n k : ℕ) (hn : 0 < n) :
    ⁅x k, chainBracket x start n⁆ =
      if k + 1 = start then chainBracket x k (n + 1)
      else if k = start + n then -chainBracket x start (n + 1) else 0 := by
  cases n with
  | zero => omega
  | succ m =>
    by_cases hl : k + 1 = start
    · rw [if_pos hl]
      subst start
      exact (chainBracket_step x k m).symm
    · rw [if_neg hl]
      by_cases hr : k = start + (m + 1)
      · rw [if_pos hr, hr]
        exact lie_chainBracket_right x hfar start (m + 1) (by omega)
      · rw [if_neg hr]
        by_cases hi : start ≤ k ∧ k < start + (m + 1)
        · exact lie_chainBracket_inside x hfar hserre start (m + 1) k hi
        · exact lie_chainBracket_far x hfar k start (m + 1) (by omega)

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalBrackets

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
open CFSGTwistedAIntervalBrackets

theorem simple_interval_raising (r : ℕ) (neg : Bool) (start n k : ℕ) (hn : 0 < n) :
    ⁅simple r neg k, interval r neg start n⁆ =
      if k + 1 = start then interval r neg k (n + 1)
      else if k = start + n then -interval r neg start (n + 1) else 0 :=
  lie_chainBracket_raising (simple r neg) (simple_lie_far r neg)
    (simple_serre_adjacent r neg) start n k hn

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
