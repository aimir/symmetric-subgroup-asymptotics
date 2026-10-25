import SymmetricSubgroupAsymptotics.LargeIndexPowerThreeEnvelopeNumerics

/-! A shared scaled class envelope for actual small-fibre actions.
The logarithmic order ceiling is compared to3^n by one dyadic induction;
the public consumers retain the actual binary/ternary factor and the
scaled component class cube, without a finite numerical menu. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SmallFibreScaledClassEnvelopeNumerics

private theorem dyadic_exponent_le (l : ℕ) (hl : 11 ≤ l) :
    (l+1)*(24*l+138)+10 ≤ 3*2^l := by
  induction l,hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    calc
      (l+1+1)*(24*(l+1)+138)+10 ≤ 2*((l+1)*(24*l+138)+10) := by nlinarith
      _ ≤ 2*(3*2^l) := Nat.mul_le_mul_left 2 ih
      _ = 3*2^(l+1) := by rw [pow_succ]; ring

theorem scaled_log_power_le_three_power (n : ℕ) (hn : 2048 ≤ n) :
    25*(n^(4*Nat.log 2 n+23))^3 ≤ 3^n := by
  let l := Nat.log 2 n
  have hl : 11 ≤ l := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (by simpa only [show (2:ℕ)^11=2048 by decide] using hn)
  have hupper : n ≤ 2^(l+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hlower : 2^l ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hexp : 6*(l+1)*(4*l+23)+10 ≤ 3*n := by
    have he : 6*(l+1)*(4*l+23)+10=(l+1)*(24*l+138)+10 := by ring
    rw [he]
    exact (dyadic_exponent_le l hl).trans (Nat.mul_le_mul_left 3 hlower)
  have hp : ((((2^(l+1))^(4*l+23))^3)^2)=2^(6*(l+1)*(4*l+23)) := by
    rw [←pow_mul,←pow_mul,←pow_mul]
    exact congrArg (fun z : ℕ => 2^z) (by ring)
  have hsquare : (25*(n^(4*l+23))^3)^2 ≤ (3^n)^2 := by
    calc
      (25*(n^(4*l+23))^3)^2 = 25^2*((n^(4*l+23))^3)^2 := mul_pow _ _ _
      _ ≤ 2^10*((((2^(l+1))^(4*l+23))^3)^2) := Nat.mul_le_mul
        (by decide : (25:ℕ)^2 ≤ 2^10)
        (Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.pow_le_pow_left hupper _) 3) 2)
      _ = 2^(6*(l+1)*(4*l+23)+10) := by
        rw [hp,←pow_add]
        exact congrArg (fun z : ℕ => 2^z) (Nat.add_comm 10 (6*(l+1)*(4*l+23)))
      _ ≤ 2^(3*n) := Nat.pow_le_pow_right (by decide) hexp
      _ = (2^3)^n := pow_mul 2 3 n
      _ ≤ (3^2)^n := Nat.pow_le_pow_left (by decide : (2:ℕ)^3 ≤ 3^2) n
      _ = (3^n)^2 := by rw [←pow_mul,←pow_mul]; exact congrArg (fun z : ℕ => 3^z) (Nat.mul_comm 2 n)
  exact (Nat.pow_le_pow_iff_left (by decide : (2:ℕ) ≠ 0)).mp hsquare

theorem binary_gap_of_scaled_cube (n B : ℕ) (hn : 1 ≤ n)
    (hB : 25*B^3 ≤ 3^n) : (2^n*B)^3 ≤ 5^(2*n-2) := by
  have htwo : (2^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have hscaled : 25*(2^n*B)^3 ≤ 25^n := by
    calc
      25*(2^n*B)^3 = 8^n*(25*B^3) := by rw [mul_pow,htwo]; ring
      _ ≤ 8^n*3^n := Nat.mul_le_mul_left _ hB
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

theorem ternary_gap_of_scaled_cube (n B : ℕ) (hn : 2 ≤ n)
    (hB : 25*B^3 ≤ 3^n) : (3^n*B)^3 ≤ 5^(3*n-2) := by
  have hbinary := binary_gap_of_scaled_cube n B (by omega) hB
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

end SymmetricSubgroupAsymptotics.SmallFibreScaledClassEnvelopeNumerics
