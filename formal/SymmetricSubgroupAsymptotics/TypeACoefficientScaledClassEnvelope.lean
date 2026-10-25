import SymmetricSubgroupAsymptotics.BinaryWeightedMultisetClassEnvelope
import Mathlib.Tactic.Ring

/-! The uniform binary coefficient code pays the scaled class budget
from rank five onward. The degree-five code and three other coefficient
capacities are selected polynomial-word calculations, not group or action
enumerations. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.TypeACoefficientScaledClassEnvelope

theorem card_codes_five : (BinaryWeightedMultisetCodes.codes 5).card=42 := by
  decide +kernel

theorem binary_scaled_cube_le (r : ℕ) (hr : 5 ≤ r) :
    25*(2*3^r)^3 ≤ 3^(2^r) := by
  have hexp : r*3+5 ≤ 2^r := by
    induction r, hr using Nat.le_induction with
    | base => decide
    | succ r hr ih =>
      rw [pow_succ]
      omega
  calc
    25*(2*3^r)^3 = 200*3^(r*3) := by rw [mul_pow,←pow_mul]; ring
    _ ≤ 3^5*3^(r*3) := Nat.mul_le_mul_right _ (by decide : 200 ≤ 3^5)
    _ = 3^(r*3+5) := by rw [←pow_add,Nat.add_comm 5 (r*3)]
    _ ≤ 3^(2^r) := Nat.pow_le_pow_right (by decide) hexp

theorem binary_rank_four_scaled_cube_le : 25*(42*2)^3 ≤ 3^(2^4) := by
  decide +kernel

theorem coefficient_heads_scaled_cube_le (r q f : ℕ)
    (h : (r=3 ∧ q=3 ∧ f=1) ∨ (r=3 ∧ q=4 ∧ f=2) ∨ (r=4 ∧ q=3 ∧ f=1)) :
    25*(((q-1).gcd (r+1)*((q-1)*(2*q-1)^r))*(2*((q-1).gcd (r+1))*f))^3 ≤
      3^(q^r) := by
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> decide +kernel

end SymmetricSubgroupAsymptotics.TypeACoefficientScaledClassEnvelope
