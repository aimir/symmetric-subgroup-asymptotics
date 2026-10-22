import SymmetricSubgroupAsymptotics.C1PrimitiveTail
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-! Elementary dyadic bounds for the actual primitive relative-three-head
  tail. These estimates do not assert an ordinary generating-rank bound. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveTernaryTailNumerics

theorem ternary_factorization_le_log2 (m : ℕ) (hm : m ≠ 0) :
    m.factorization 3 ≤ Nat.log2 m := by
  rw [Nat.log2_eq_log_two]
  apply (Nat.le_log_iff_pow_le (by decide : 1 < 2) hm).2
  exact (Nat.pow_le_pow_left (by decide : 2 ≤ 3) _).trans (Nat.ordProj_le 3 hm)

theorem ternary_factorization_le_of_lt_pow {m b : ℕ} (hm : m ≠ 0)
    (h : m < 3 ^ (b + 1)) : m.factorization 3 ≤ b := by
  by_contra hn
  have hp : 3 ^ (b + 1) ≤ 3 ^ m.factorization 3 :=
    pow_le_pow_right₀ (by decide : 1 ≤ 3) (by omega)
  have ho := Nat.ordProj_le 3 hm
  omega

theorem dyadic_quadratic_tail (k : ℕ) :
    20 * ((k + 11)^2 + 2*(k + 11)) < 3*2^(k + 10) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hp : 2^(k.succ+10)=2^(k+10)*2 := by
        rw [show k.succ+10=k+10+1 by omega, pow_succ]
      rw [hp]
      have hg : (k + 12)^2 + 2*(k + 12) ≤
          2*((k + 11)^2 + 2*(k + 11)) := by nlinarith
      nlinarith

theorem quadratic_log_tail {w : ℕ} (hw : 1024 ≤ w) :
    20*((Nat.log2 w + 1)^2 + 2*(Nat.log2 w + 1)) < 3*w := by
  have hw0 : w ≠ 0 := by omega
  have hten : 10 ≤ Nat.log2 w := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) hw0).2 (by norm_num; omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hten
  have hp : 2^Nat.log2 w ≤ w := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) hw0).1 le_rfl
  have ht : 20*((Nat.log2 w + 1)^2 + 2*(Nat.log2 w + 1)) <
      3*2^Nat.log2 w := by
    rw [hk]
    simpa only [show 10+k+1 = k+11 by omega, show 10+k = k+10 by omega] using
      dyadic_quadratic_tail k
  exact ht.trans_le (Nat.mul_le_mul_left 3 hp)

theorem log2_degree_upper {w : ℕ} (_hw : w ≠ 0) : w ≤ 2^(Nat.log2 w + 1) := by
  rw [Nat.log2_eq_log_two]
  exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) w).le

theorem outer_wreath_order_dyadic {ell out k w : ℕ}
    (hell : 2 ≤ ell) (hd : ell^k ≤ w) (hout : out ≤ ell^2) :
    out^k*k.factorial ≤ 2^((Nat.log2 w + 1)^2 + 2*(Nat.log2 w + 1)) := by
  have hw0 : w ≠ 0 := by
    have hp := pow_pos (show 0 < ell by omega) k
    omega
  have hk : k ≤ Nat.log2 w := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) hw0).2
      ((Nat.pow_le_pow_left hell k).trans hd)
  have hf : k.factorial ≤ 2^(k*k) := calc
    k.factorial ≤ k^k := k.factorial_le_pow
    _ ≤ (2^k)^k := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := k)).le k
    _ = 2^(k*k) := by rw [pow_mul]
  have hs : out^k ≤ w^2 := calc
    out^k ≤ (ell^2)^k := Nat.pow_le_pow_left hout k
    _ = (ell^k)^2 := by rw [← pow_mul, ← pow_mul]; congr 1; omega
    _ ≤ w^2 := Nat.pow_le_pow_left hd 2
  have hu := log2_degree_upper hw0
  calc
    out^k*k.factorial ≤ w^2 * 2^(k*k) := Nat.mul_le_mul hs hf
    _ ≤ (2^(Nat.log2 w+1))^2 * 2^((Nat.log2 w+1)^2) := by
      apply Nat.mul_le_mul (Nat.pow_le_pow_left hu 2)
      apply pow_le_pow_right₀ (by decide : 1 ≤ 2)
      nlinarith
    _ = 2^((Nat.log2 w+1)^2 + 2*(Nat.log2 w+1)) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

end SymmetricSubgroupAsymptotics.CFSGPrimitiveTernaryTailNumerics
