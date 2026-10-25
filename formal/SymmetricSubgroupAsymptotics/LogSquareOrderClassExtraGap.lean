import SymmetricSubgroupAsymptotics.LogSquareOrderSubgroupClassBound

/-! The actual power-form order proof already fits a base-four
majorant. Its comparison to five leaves one extra exponent at every
degree at least 1024, for the SAME arbitrary subgroup. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.LogSquareOrderClassExtraGap

private theorem four_power_le (n : ℕ) (hn : 9 ≤ n) : 4^(n-1) ≤ 5^(n-2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      4^((n+1)-1) = 4*4^(n-1) := by
        rw [show (n+1)-1=(n-1)+1 by omega, pow_succ']
      _ ≤ 5*5^(n-2) := Nat.mul_le_mul (by decide) ih
      _ = 5^((n+1)-2) := by rw [← pow_succ']; congr 1; omega

theorem order_cube_le (n : ℕ) (hn : 1024 ≤ n) :
    (n^(4*Nat.log 2 n+2))^3 ≤ 5^(n-2) := by
  let l := Nat.log 2 n
  have hl : 10 ≤ l := Nat.le_log_of_pow_le (by decide : 1 < 2) (by simpa using hn)
  have hnupper : n ≤ 2^(l+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hlower : 2^l ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hsmall := LogSquareOrderClassNumerics.dyadic_exponent_le l hl
  have he : 3*(l+1)*(4*l+2) ≤ 2*(n-1) := by omega
  calc
    (n^(4*Nat.log 2 n+2))^3 ≤ ((2^(l+1))^(4*l+2))^3 :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_left hnupper _) _
    _ = 2^(3*(l+1)*(4*l+2)) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
    _ ≤ 2^(2*(n-1)) := Nat.pow_le_pow_right (by decide) he
    _ = 4^(n-1) := by rw [pow_mul]; norm_num
    _ ≤ 5^(n-2) := four_power_le n (by omega)

theorem subgroup_class_cube_le {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 1024 ≤ n) (horder : Nat.card G ≤ n^(4*Nat.log 2 n+2))
    (H : Subgroup G) : Nat.card (ConjClasses H)^3 ≤ 5^(n-2) := by
  have hc : Nat.card (ConjClasses H) ≤ n^(4*Nat.log 2 n+2) :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans
      (H.card_le_card_group.trans horder)
  exact (Nat.pow_le_pow_left hc 3).trans (order_cube_le n hn)

end SymmetricSubgroupAsymptotics.LogSquareOrderClassExtraGap
