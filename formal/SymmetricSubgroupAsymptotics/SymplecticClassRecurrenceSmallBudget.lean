import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Arithmetic assembly for the five small classical parameters. The
structural recurrence and fixed-free class bounds are explicit premises;
this module does not claim that their remaining module-counting input
has already been discharged. -/
set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.SymplecticClassRecurrenceSmallBudget

theorem binary_through_rankFour (s p : ℕ → ℕ)
    (hs₁ : s 1 ≤ 6) (hp₁ : p 1 ≤ 2)
    (hstep : ∀ r : ℕ, 1 ≤ r → p (r+1) ≤ 2*(s r+p r))
    (hfree : ∀ r : ℕ, 2 ≤ r → s r ≤ 2^(2*r-1)+p r) :
    p 2 ≤ 16 ∧ s 2 ≤ 24 ∧ p 3 ≤ 80 ∧ s 3 ≤ 112 ∧
      p 4 ≤ 384 ∧ s 4 ≤ 512 ∧ s 4+p 4 ≤ 896 := by
  have hp₂ := hstep 1 (by decide)
  have hp₃ := hstep 2 (by decide)
  have hp₄ := hstep 3 (by decide)
  have hs₂ := hfree 2 (by decide)
  have hs₃ := hfree 3 (by decide)
  have hs₄ := hfree 4 (by decide)
  norm_num at hp₂ hp₃ hp₄ hs₂ hs₃ hs₄
  omega

theorem four_rankTwo (s p : ℕ → ℕ)
    (hs₁ : s 1 ≤ 8) (hp₁ : p 1 ≤ 4)
    (hstep : p 2 ≤ 4*(s 1+p 1)) (hfree : s 2 ≤ 128+p 2) :
    p 2 ≤ 48 ∧ s 2 ≤ 176 := by
  omega

end SymmetricSubgroupAsymptotics.SymplecticClassRecurrenceSmallBudget
