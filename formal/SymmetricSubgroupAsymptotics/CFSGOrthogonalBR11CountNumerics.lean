import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Coarse q-element fibres already separate the common-neighbour
counts. Exact projective cone cardinalities are unnecessary. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBR11CountNumerics

theorem quartic_gap (q : ℕ) (hq : 3 ≤ q) : q * (q + 1) ^ 2 + 1 < q ^ 4 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hq
  nlinarith [Nat.zero_le (t ^ 2), Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 4)]

theorem first_residual_large (q c : ℕ) (hq : 3 ≤ q) (h : q ^ 2 - 1 ≤ c * q) : 1 < c := by
  have hp : 1 ≤ q ^ 2 := by nlinarith
  have hb : q ^ 2 ≤ c * q + 1 := by omega
  by_contra hn
  have hc : c ≤ 1 := by omega
  have hm := Nat.mul_le_mul_right q hc
  nlinarith

theorem higher_residual_large (q c m : ℕ) (hq : 3 ≤ q) (hm : 2 ≤ m)
    (h : q ^ (2 * m) - 1 ≤ c * q) : (q + 1) ^ 2 < c := by
  have hq1 : 1 ≤ q := by omega
  have hp : 1 ≤ q ^ (2 * m) := Nat.one_le_pow _ _ hq1
  have hb : q ^ (2 * m) ≤ c * q + 1 := by omega
  have hfour : q ^ 4 ≤ q ^ (2 * m) := Nat.pow_le_pow_right hq1 (by omega)
  by_contra hn
  have hc : c ≤ (q + 1) ^ 2 := by omega
  have hm' := Nat.mul_le_mul_right q hc
  have hs := quartic_gap q hq
  rw [Nat.mul_comm q ((q + 1) ^ 2)] at hs
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBR11CountNumerics
