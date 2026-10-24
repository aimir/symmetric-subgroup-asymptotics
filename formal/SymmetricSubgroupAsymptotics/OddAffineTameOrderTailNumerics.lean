import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Uniform polynomial budgets for an odd-affine local degree in the
binary window [2^k,2^(k+1)), k>=7. The faithful affine order has real
logarithm at most (2/3)(k+1)(k+2). Both scalar regimes are paid by
induction, with no enumeration of prime characteristics or top degrees. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.OddAffineTameOrderTailNumerics

theorem small_log_budget (k : ℕ) (hk : 7 ≤ k) :
    (k+1)*((k+1)*(k+2)+6)^2 ≤ 3*4^k := by
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hshift : k = (k-7)+7 := by omega
      have heq : 4*((k+1)*((k+1)*(k+2)+6)^2) =
          ((k+1)+1)*(((k+1)+1)*((k+1)+2)+6)^2+
          (3*(k-7)^5+121*(k-7)^4+1973*(k-7)^3+
            16223*(k-7)^2+67152*(k-7)+111744) := by
        rw [hshift]
        simp only [Nat.add_sub_cancel]
        ring
      have hstep : ((k+1)+1)*(((k+1)+1)*((k+1)+2)+6)^2 ≤
          4*((k+1)*((k+1)*(k+2)+6)^2) := by rw [heq]; omega
      calc
        ((k+1)+1)*(((k+1)+1)*((k+1)+2)+6)^2 ≤
            4*((k+1)*((k+1)*(k+2)+6)^2) := hstep
        _ ≤ 4*(3*4^k) := Nat.mul_le_mul_left 4 ih
        _ = 3*4^(k+1) := by rw [pow_succ]; ring

theorem large_log_budget (k : ℕ) (hk : 7 ≤ k) :
    2*(2*(k+1)*(k+2)+3)^2 ≤ 3*4^k := by
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hshift : k = (k-7)+7 := by omega
      have heq : 4*(2*(2*(k+1)*(k+2)+3)^2) =
          2*(2*((k+1)+1)*((k+1)+2)+3)^2+
          (24*(k-7)^4+784*(k-7)^3+9600*(k-7)^2+52152*(k-7)+105894) := by
        rw [hshift]
        simp only [Nat.add_sub_cancel]
        ring
      have hstep : 2*(2*((k+1)+1)*((k+1)+2)+3)^2 ≤
          4*(2*(2*(k+1)*(k+2)+3)^2) := by rw [heq]; omega
      calc
        2*(2*((k+1)+1)*((k+1)+2)+3)^2 ≤
            4*(2*(2*(k+1)*(k+2)+3)^2) := hstep
        _ ≤ 4*(3*4^k) := Nat.mul_le_mul_left 4 ih
        _ = 3*4^(k+1) := by rw [pow_succ]; ring

end SymmetricSubgroupAsymptotics.OddAffineTameOrderTailNumerics
