import SymmetricSubgroupAsymptotics.LogSquareOrderClassNumerics
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.ConjFinite

/-! A wider uniform order budget for primitive socle index forms. The
comparison uses 2^9 <= 5^4, retaining enough margin to absorb the linear
term in the logarithmic exponent. No degree menu is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.WideLogSquareOrderClassNumerics

theorem dyadic_exponent_le (l : ℕ) (hl : 10 ≤ l) :
    12*(l+1)*(4*l+24)+9 ≤ 9*2^l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    calc
      12*(l+1+1)*(4*(l+1)+24)+9 ≤
          2*(12*(l+1)*(4*l+24)+9) := by nlinarith
      _ ≤ 2*(9*2^l) := Nat.mul_le_mul_left 2 ih
      _ = 9*2^(l+1) := by rw [pow_succ]; ring

theorem order_cube_le_garonziMaroti (n : ℕ) (hn : 1024 ≤ n) :
    (n^(4*Nat.log 2 n+24))^3 ≤ 5^(n-1) := by
  let l := Nat.log 2 n
  have hl : 10 ≤ l := Nat.le_log_of_pow_le (by decide : 1 < 2) (by simpa using hn)
  have hnupper : n ≤ 2^(l+1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hlower : 2^l ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hsmall := dyadic_exponent_le l hl
  have hexponent : 12*(l+1)*(4*l+24) ≤ 9*(n-1) := by omega
  have hfour : ((n^(4*Nat.log 2 n+24))^3)^4 ≤ (5^(n-1))^4 := by
    calc
      ((n^(4*Nat.log 2 n+24))^3)^4 ≤ (((2^(l+1))^(4*l+24))^3)^4 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.pow_le_pow_left hnupper _) _) _
      _ = 2^(12*(l+1)*(4*l+24)) := by
        rw [←pow_mul, ←pow_mul, ←pow_mul]
        congr 1
        ring
      _ ≤ 2^(9*(n-1)) := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexponent
      _ = (2^9)^(n-1) := by rw [pow_mul]
      _ ≤ (5^4)^(n-1) := Nat.pow_le_pow_left (by decide : (2 : ℕ)^9 ≤ 5^4) _
      _ = (5^(n-1))^4 := by rw [←pow_mul, ←pow_mul]; congr 1; omega
  by_contra h
  have hlt := Nat.pow_lt_pow_left (by omega : 5^(n-1) < (n^(4*Nat.log 2 n+24))^3)
    (by decide : 4 ≠ 0)
  omega

theorem subgroup_class_cube_le {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 1024 ≤ n) (horder : Nat.card G ≤ n^(4*Nat.log 2 n+24))
    (H : Subgroup G) : Nat.card (ConjClasses H)^3 ≤ 5^(n-1) := by
  have hc : Nat.card (ConjClasses H) ≤ n^(4*Nat.log 2 n+24) :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans
      (H.card_le_card_group.trans horder)
  exact (Nat.pow_le_pow_left hc 3).trans (order_cube_le_garonziMaroti n hn)

end SymmetricSubgroupAsymptotics.WideLogSquareOrderClassNumerics
