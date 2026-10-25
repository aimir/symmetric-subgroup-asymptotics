import SymmetricSubgroupAsymptotics.External.CFSG.Parameters
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Uniform field-exponent bounds from an actual proper-index budget.
These are arithmetic implications, independent of a model or census. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.PrimePowerProperIndexExponentBound

theorem binary_power_le (q : CFSG.PrimePower) (r n : ℕ)
    (hindex : 2*q.order^r ≤ n) : 2^(q.exponent*r+1) ≤ n := by
  have hq : 2^q.exponent ≤ q.order := Nat.pow_le_pow_left q.prime_isPrime.two_le _
  calc
    _ = 2*(2^q.exponent)^r := by rw [pow_add,pow_one,pow_mul]; ring
    _ ≤ 2*q.order^r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq r)
    _ ≤ _ := hindex

theorem exponent_le (q : CFSG.PrimePower) (r n t : ℕ)
    (hindex : 2*q.order^r ≤ n) (hn : n < 2^((t+1)*r+1)) : q.exponent ≤ t := by
  by_contra hh
  have he : (t+1)*r+1 ≤ q.exponent*r+1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right r (show t+1≤q.exponent by omega)) 1
  have hp := (Nat.pow_le_pow_right (by decide : 0<2) he).trans
    (binary_power_le q r n hindex)
  omega

end SymmetricSubgroupAsymptotics.PrimePowerProperIndexExponentBound
