import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A power-66 order packet has an exponential class reserve at every
actual index at least2048. One dyadic induction proves the integer
comparison; no numerical menu, parameter rows or increased settings
are used. Binary and ternary block factors remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.LargeIndexPowerThreeEnvelopeNumerics

private theorem dyadic_exponent_le (l : ℕ) (hl : 11 ≤ l) :
    396*(l+1)+10 ≤ 3*2^l := by
  induction l,hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    calc
      396*(l+1+1)+10 ≤ 2*(396*(l+1)+10) := by omega
      _ ≤ 2*(3*2^l) := Nat.mul_le_mul_left 2 ih
      _ = 3*2^(l+1) := by rw [pow_succ]; ring

theorem scaled_power_le_three_power (n : ℕ) (hn : 2048 ≤ n) :
    25*n^198 ≤ 3^n := by
  let l := Nat.log 2 n
  have hl : 11 ≤ l := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (by simpa only [show (2:ℕ)^11=2048 by decide] using hn)
  have hupper : n ≤ 2^(l+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hlower : 2^l ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hexp : 396*(l+1)+10 ≤ 3*n :=
    (dyadic_exponent_le l hl).trans (Nat.mul_le_mul_left 3 hlower)
  have hp : (((2^(l+1))^198)^2)=2^(396*(l+1)) := by
    rw [←pow_mul,←pow_mul]
    congr 1
    ring
  have hsquare : (25*n^198)^2 ≤ (3^n)^2 := by
    calc
      (25*n^198)^2 = 25^2*(n^198)^2 := mul_pow _ _ _
      _ ≤ 2^10*(((2^(l+1))^198)^2) := Nat.mul_le_mul
        (by decide : (25:ℕ)^2 ≤ 2^10)
        (Nat.pow_le_pow_left (Nat.pow_le_pow_left hupper 198) 2)
      _ = 2^(396*(l+1)+10) := by
        rw [hp,←pow_add]
        exact congrArg (fun z : ℕ => 2^z) (Nat.add_comm 10 (396*(l+1)))
      _ ≤ 2^(3*n) := Nat.pow_le_pow_right (by decide) hexp
      _ = (2^3)^n := pow_mul 2 3 n
      _ ≤ (3^2)^n := Nat.pow_le_pow_left (by decide : (2:ℕ)^3 ≤ 3^2) n
      _ = (3^n)^2 := by rw [←pow_mul,←pow_mul]; congr 1; omega
  exact (Nat.pow_le_pow_iff_left (by decide : (2:ℕ) ≠ 0)).mp hsquare

theorem binary_product_cube_gap (n B : ℕ) (hn : 2048 ≤ n) (hB : B ≤ n^66) :
    (2^n*B)^3 ≤ 5^(2*n-2) := by
  have hcube : B^3 ≤ n^198 := by
    calc
      B^3 ≤ (n^66)^3 := Nat.pow_le_pow_left hB 3
      _ = n^198 := by rw [←pow_mul]
  have henv : 25*B^3 ≤ 3^n :=
    (Nat.mul_le_mul_left 25 hcube).trans (scaled_power_le_three_power n hn)
  have htwo : (2^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have hscaled : 25*(2^n*B)^3 ≤ 25^n := by
    calc
      25*(2^n*B)^3 = 8^n*(25*B^3) := by rw [mul_pow,htwo]; ring
      _ ≤ 8^n*3^n := Nat.mul_le_mul_left _ henv
      _ = 24^n := by rw [←mul_pow]; norm_num
      _ ≤ 25^n := Nat.pow_le_pow_left (by decide) n
  have he : 25*5^(2*n-2)=25^n := by
    calc
      25*5^(2*n-2) = 5^(2*n) := by
        rw [show (25:ℕ)=5^2 by decide,←pow_add]
        congr 1
        omega
      _ = (5^2)^n := pow_mul 5 2 n
      _ = 25^n := by norm_num
  rw [←he] at hscaled
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

theorem ternary_product_cube_gap (n B : ℕ) (hn : 2048 ≤ n) (hB : B ≤ n^66) :
    (3^n*B)^3 ≤ 5^(3*n-2) := by
  have hbinary := binary_product_cube_gap n B hn hB
  have hthree : (3^n)^3=27^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have htwo : (2^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have h27 : (3^n)^3 ≤ 5^n*(2^n)^3 := by
    rw [hthree,htwo,←mul_pow]
    exact Nat.pow_le_pow_left (by decide : (27:ℕ) ≤ 5*8) n
  calc
    (3^n*B)^3 = (3^n)^3*B^3 := mul_pow _ _ _
    _ ≤ (5^n*(2^n)^3)*B^3 := Nat.mul_le_mul_right _ h27
    _ = 5^n*(2^n*B)^3 := by rw [mul_pow]; ring
    _ ≤ 5^n*5^(2*n-2) := Nat.mul_le_mul_left _ hbinary
    _ = 5^(3*n-2) := by rw [←pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.LargeIndexPowerThreeEnvelopeNumerics
