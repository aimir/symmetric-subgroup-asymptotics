import SymmetricSubgroupAsymptotics.CharacterPairMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# Turning retained four-selection incidence into the pair moment

This analytic endpoint separates the proved original-character counting
from its remaining physical input. An incidence budget A times the family
size gives coefficient 7+A^(1/4), with every duplicate mark still retained.
In the E8 application A=6N; the physical incidence is not a premise that
may be dropped merely because the local reversible model exists.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.CharacterPairMoment

variable {B : Type*} [Fintype B] {I V : B → Type*}
    [∀ b, Finite (I b)] [∀ b, AddCommGroup (V b)]
    [∀ b, Module (ZMod 2) (V b)] [∀ b, Finite (V b)]
    (f : ∀ b, I b → V b)

theorem aggregate_excess_le_of_incidence (hzero : ∀ b i, f b i ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hinc : (∑ b, (Nat.card (CharacterIndependentSelections.Frame (f b) 4) : ℝ)) ≤
      C ^ 4 * Fintype.card B) :
    (∑ b, (excess (f b) : ℝ)) ≤ C * Fintype.card B := by
  have hp : (∑ b, (excess (f b) : ℝ)) ^ 4 ≤ (Fintype.card B : ℝ) ^ 3 *
      ∑ b, (Nat.card (CharacterIndependentSelections.Frame (f b) 4) : ℝ) := by
    exact_mod_cast aggregate_excess_pow_four_le f hzero
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
  calc
    _ ≤ (Fintype.card B : ℝ) ^ 3 *
        ∑ b, (Nat.card (CharacterIndependentSelections.Frame (f b) 4) : ℝ) := hp
    _ ≤ (Fintype.card B : ℝ) ^ 3 * (C ^ 4 * Fintype.card B) :=
      mul_le_mul_of_nonneg_left hinc (by positivity)
    _ = (C * Fintype.card B) ^ 4 := by ring

/-- Every original occurrence is charged either to seven per group,
an actual duplicate pair, or the fourth moment of actual selections. -/
theorem aggregate_card_le_of_incidence (hzero : ∀ b i, f b i ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hinc : (∑ b, (Nat.card (CharacterIndependentSelections.Frame (f b) 4) : ℝ)) ≤
      C ^ 4 * Fintype.card B) :
    (∑ b, (Nat.card (I b) : ℝ)) ≤ (7 + C) * Fintype.card B +
      ∑ b, (Nat.card (CharacterCollisionCount.Collision (f b)) : ℝ) := by
  have hb : (∑ b, (Nat.card (I b) : ℝ)) ≤ 7 * Fintype.card B +
      (∑ b, (Nat.card (CharacterCollisionCount.Collision (f b)) : ℝ)) +
      ∑ b, (excess (f b) : ℝ) := by
    exact_mod_cast aggregate_card_le f
  have he := aggregate_excess_le_of_incidence f hzero C hC hinc
  nlinarith

theorem aggregate_card_le_quarter_power (hzero : ∀ b i, f b i ≠ 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hinc : (∑ b, (Nat.card (CharacterIndependentSelections.Frame (f b) 4) : ℝ)) ≤
      A * Fintype.card B) :
    (∑ b, (Nat.card (I b) : ℝ)) ≤ (7 + A ^ (1 / 4 : ℝ)) * Fintype.card B +
      ∑ b, (Nat.card (CharacterCollisionCount.Collision (f b)) : ℝ) := by
  apply aggregate_card_le_of_incidence f hzero (A ^ (1 / 4 : ℝ))
    (Real.rpow_nonneg hA _)
  have hp : (A ^ (1 / 4 : ℝ)) ^ 4 = A := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hA (by decide : (4 : ℕ) ≠ 0)
  rw [hp]
  exact hinc

end SymmetricSubgroupAsymptotics.CharacterPairMoment
