import SymmetricSubgroupAsymptotics.LargePrimitiveWideSmallFibreClassNumerics

/-! One exponent of genuine saving in the large intermediate-top
binary/ternary tail. The earlier checked numerical bounds remain
unchanged; this companion retains the same cutoff and order budget. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.LargeSmallFibreSubnormalGapNumerics

private theorem four_pow_succ_le_five_pow (m : ℕ) (hm : 7 ≤ m) :
    4 ^ (m + 1) ≤ 5 ^ m := by
  induction m,hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    calc
      4 ^ (m + 1 + 1) = 4 ^ (m + 1) * 4 := pow_succ _ _
      _ ≤ 5 ^ m * 5 := Nat.mul_le_mul ih (by decide)
      _ = 5 ^ (m + 1) := (pow_succ _ _).symm

theorem binary_product_cube_gap (n a : ℕ) (hn : 4096 ≤ n)
    (horder : a ≤ n ^ (4 * Nat.log 2 n + 30)) :
    (2 ^ n * a) ^ 3 ≤ 5 ^ (2 * n - 2) := by
  let m := Nat.log 2 n
  have hm : 12 ≤ m := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (show 2 ^ 12 ≤ n by simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using hn)
  have hn0 : n ≠ 0 := by omega
  have hlow : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn0
  have hupp : n ≤ 2 ^ (m + 1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have ha : a ≤ 2 ^ ((m + 1) * (4 * m + 30)) := by
    apply horder.trans
    simpa only [m,pow_mul] using Nat.pow_le_pow_left hupp (4 * m + 30)
  have hb : 3 * (m + 1) * (4 * m + 30) + 2 ≤ n :=
    (LargePrimitiveWideSmallFibreClassNumerics.dyadic_budget m hm).trans hlow
  rw [Nat.mul_assoc] at hb
  have he : (n + (m + 1) * (4 * m + 30)) * 3 ≤ 2 * (2 * n - 1) := by omega
  have hfour : 4 ^ (2 * n - 1) ≤ 5 ^ (2 * n - 2) := by
    have h : 2 * n - 1 = (2 * n - 2) + 1 := by omega
    rw [h]
    exact four_pow_succ_le_five_pow _ (by omega)
  calc
    (2 ^ n * a) ^ 3 ≤ (2 ^ n * 2 ^ ((m + 1) * (4 * m + 30))) ^ 3 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ ha) 3
    _ = 2 ^ ((n + (m + 1) * (4 * m + 30)) * 3) := by rw [← pow_add,← pow_mul]
    _ ≤ 2 ^ (2 * (2 * n - 1)) := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
    _ = 4 ^ (2 * n - 1) := by rw [show (4 : ℕ) = 2 ^ 2 by decide,pow_mul]
    _ ≤ 5 ^ (2 * n - 2) := hfour

theorem ternary_product_cube_gap (n a : ℕ) (hn : 4096 ≤ n)
    (horder : a ≤ n ^ (4 * Nat.log 2 n + 30)) :
    (3 ^ n * a) ^ 3 ≤ 5 ^ (3 * n - 2) := by
  have hbinary := binary_product_cube_gap n a hn horder
  have hthree : (3 ^ n) ^ 3 = 27 ^ n := by
    rw [← pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have htwo : (2 ^ n) ^ 3 = 8 ^ n := by
    rw [← pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have h27 : (3 ^ n) ^ 3 ≤ 5 ^ n * (2 ^ n) ^ 3 := by
    rw [hthree,htwo,← mul_pow]
    exact Nat.pow_le_pow_left (by decide : 27 ≤ 5 * 8) n
  calc
    (3 ^ n * a) ^ 3 = (3 ^ n) ^ 3 * a ^ 3 := mul_pow _ _ _
    _ ≤ (5 ^ n * (2 ^ n) ^ 3) * a ^ 3 := Nat.mul_le_mul_right _ h27
    _ = 5 ^ n * (2 ^ n * a) ^ 3 := by rw [mul_pow]; ring
    _ ≤ 5 ^ n * 5 ^ (2 * n - 2) := Nat.mul_le_mul_left _ hbinary
    _ = 5 ^ (3 * n - 2) := by rw [← pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.LargeSmallFibreSubnormalGapNumerics
