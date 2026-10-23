import SymmetricSubgroupAsymptotics.CFSGTrialityTripleFixedRoots
import Mathlib.FieldTheory.Finite.Basic

/-! A uniform actual cubic-field torus parameter for triality. Even
q=2 gives at least seven units, so the square action is nontrivial. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityCubicFieldWitness

theorem exists_cubic_unit_square_ne_one (q : CFSG.PrimePower) :
    ∃ a : (q.Extension 3)ˣ, (a : q.Extension 3) ^ 2 ≠ 1 := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hc : 2 < Nat.card (q.Extension 3)ˣ := by
    rw [Nat.card_units, CFSGTrialityTripleFixedRoots.extension_three_card]
    have hcube : 8 ≤ q.order ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  obtain ⟨a, ha⟩ := exists_pow_ne_one_of_isCyclic (G := (q.Extension 3)ˣ) (k := 2) (by decide) hc
  refine ⟨a, ?_⟩
  intro he
  apply ha
  apply Units.ext
  exact he

theorem exists_cubic_square_ne_one (q : CFSG.PrimePower) :
    ∃ a : q.Extension 3, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  obtain ⟨a, ha⟩ := exists_cubic_unit_square_ne_one q
  exact ⟨a, Units.ne_zero a, ha⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityCubicFieldWitness
