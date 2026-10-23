import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A quadratic group-order ceiling suffices for the GM cube from
degree ten onward. The polynomial/exponential comparison is uniform. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.QuadraticOrderClassNumerics

theorem sixth_power_step (n : ℕ) (hn : 10 ≤ n) : (n+1)^6 ≤ 5*n^6 := by
  have hlinear : 10*(n+1) ≤ 11*n := by omega
  have hpower := Nat.pow_le_pow_left hlinear 6
  have hratio : (11:ℕ)^6 ≤ 5*10^6 := by norm_num
  have hbound : 10^6*(n+1)^6 ≤ 10^6*(5*n^6) := by
    calc
      10^6*(n+1)^6 = (10*(n+1))^6 := (mul_pow _ _ _).symm
      _ ≤ (11*n)^6 := hpower
      _ = 11^6*n^6 := mul_pow _ _ _
      _ ≤ (5*10^6)*n^6 := Nat.mul_le_mul_right _ hratio
      _ = 10^6*(5*n^6) := by ring
  exact Nat.le_of_mul_le_mul_left hbound (by norm_num : 0 < (10:ℕ)^6)

theorem sixth_power_le_garonziMaroti (n : ℕ) (hn : 10 ≤ n) : n^6 ≤ 5^(n-1) := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      (n+1)^6 ≤ 5*n^6 := sixth_power_step n hn
      _ ≤ 5*5^(n-1) := Nat.mul_le_mul_left 5 ih
      _ = 5^((n+1)-1) := by
        rw [show (n+1)-1=(n-1)+1 by omega, pow_succ]
        exact Nat.mul_comm _ _

end SymmetricSubgroupAsymptotics.QuadraticOrderClassNumerics
