import SymmetricSubgroupAsymptotics.LogSquareOrderClassNumerics
import Mathlib.Data.Nat.Factorial.Basic

/-! A uniform cube budget for a bounded-dimensional simple component
in a primitive index form. The component order times outer order may be
as large as the 66th power of its index; the actual factorial on the
number of factors is retained. No finite group census enters. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BoundedComponentSocleClassNumerics

theorem factorial_le_pow_pred (k : ℕ) (hk : 1 ≤ k) : k.factorial ≤ k^(k-1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc
      (k+1).factorial = (k+1)*k.factorial := Nat.factorial_succ k
      _ ≤ (k+1)*(k+1)^(k-1) := Nat.mul_le_mul_left _
        (ih.trans (Nat.pow_le_pow_left (Nat.le_succ k) _))
      _ = (k+1)^k := by
        rw [←pow_succ']
        congr 1
        omega
      _ = (k+1)^(k+1-1) := by congr 1

theorem component_order_le (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) :
    (m^66)^k*k.factorial ≤ (m^k)^(65+k) := by
  have hkn : k ≤ m^k := k.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hm k)
  have hf : k.factorial ≤ (m^k)^(k-1) :=
    (factorial_le_pow_pred k hk).trans (Nat.pow_le_pow_left hkn _)
  calc
    (m^66)^k*k.factorial ≤ (m^k)^66*(m^k)^(k-1) := by
      have he : (m^66)^k=(m^k)^66 := by rw [←pow_mul, ←pow_mul, Nat.mul_comm]
      rw [he]
      exact Nat.mul_le_mul_left _ hf
    _ = (m^k)^(66+(k-1)) := (pow_add _ _ _).symm
    _ = (m^k)^(65+k) := by congr 1; omega

private theorem dyadic_component_exponent_le (l : ℕ) (hl : 11 ≤ l) :
    12*(l+1)*(65+l)+9 ≤ 9*2^l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    calc
      12*(l+1+1)*(65+(l+1))+9 ≤ 2*(12*(l+1)*(65+l)+9) := by nlinarith
      _ ≤ 2*(9*2^l) := Nat.mul_le_mul_left 2 ih
      _ = 9*2^(l+1) := by rw [pow_succ]; ring

theorem component_cube_le_garonziMaroti (m k : ℕ) (hm : 5 ≤ m) (hk : 1 ≤ k)
    (hn : 1024 ≤ m^k) : ((m^66)^k*k.factorial)^3 ≤ 5^(m^k-1) := by
  let n := m^k
  let l := Nat.log 2 n
  have hm2 : 2 ≤ m := by omega
  have hnpos : 0 < n := by dsimp only [n]; exact pow_pos (by omega) _
  have hl : 10 ≤ l := Nat.le_log_of_pow_le (by decide) hn
  have hnupper : n < 2^(l+1) := Nat.lt_pow_succ_log_self (by decide) n
  have hlower : 2^l ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hkl : k ≤ l := Nat.le_log_of_pow_le (by decide)
    (by exact (Nat.pow_le_pow_left hm2 k))
  have hdyadic : 12*(l+1)*(65+k)+9 ≤ 9*2^l := by
    by_cases hlarge : 11 ≤ l
    · exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega : 65+k ≤ 65+l)) 9).trans
        (dyadic_component_exponent_le l hlarge)
    · have hl10 : l=10 := by omega
      have hk4 : k ≤ 4 := by
        by_contra h
        have h5 : (5 : ℕ)^5 ≤ n :=
          (Nat.pow_le_pow_right (by decide) (by omega : 5 ≤ k)).trans
            (Nat.pow_le_pow_left hm k)
        rw [hl10] at hnupper
        norm_num at h5 hnupper
        omega
      rw [hl10]
      norm_num
      omega
  have hexp : 12*(l+1)*(65+k) ≤ 9*(n-1) := by omega
  have hfour : ((n^(65+k))^3)^4 ≤ (5^(n-1))^4 := by
    calc
      ((n^(65+k))^3)^4 ≤ (((2^(l+1))^(65+k))^3)^4 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.pow_le_pow_left hnupper.le _) _) _
      _ = 2^(12*(l+1)*(65+k)) := by
        rw [←pow_mul, ←pow_mul, ←pow_mul]
        congr 1
        ring
      _ ≤ 2^(9*(n-1)) := Nat.pow_le_pow_right (by decide) hexp
      _ = (2^9)^(n-1) := pow_mul _ _ _
      _ ≤ (5^4)^(n-1) := Nat.pow_le_pow_left (by decide : (2 : ℕ)^9 ≤ 5^4) _
      _ = (5^(n-1))^4 := by rw [←pow_mul, ←pow_mul]; congr 1; omega
  have hcube : (n^(65+k))^3 ≤ 5^(n-1) := by
    by_contra h
    have hlt := Nat.pow_lt_pow_left (by omega : 5^(n-1) < (n^(65+k))^3)
      (by decide : 4 ≠ 0)
    omega
  exact (Nat.pow_le_pow_left (component_order_le m k hm2 hk) 3).trans hcube

end SymmetricSubgroupAsymptotics.BoundedComponentSocleClassNumerics
