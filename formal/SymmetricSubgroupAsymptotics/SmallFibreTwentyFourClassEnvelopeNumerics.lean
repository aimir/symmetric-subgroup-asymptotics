import SymmetricSubgroupAsymptotics.SmallFibreScaledClassEnvelopeNumerics

/-! A separate24-reserve envelope. The exact binary ratio is24/25,
so24*B^3≤3^n already pays the same extra exponent. Existing25-reserve
APIs are unchanged; this file makes no model class-count assertion. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SmallFibreTwentyFourClassEnvelopeNumerics

theorem binary_gap_of_scaled_cube (n B : ℕ) (hn : 1≤n)
    (hB : 24*B^3≤3^n) : (2^n*B)^3≤5^(2*n-2) := by
  have htwo : (2^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have hscaled : 24*(2^n*B)^3≤24^n := by
    calc
      24*(2^n*B)^3=8^n*(24*B^3) := by rw [mul_pow,htwo]; ring
      _≤8^n*3^n := Nat.mul_le_mul_left _ hB
      _=24^n := by rw [←mul_pow]; norm_num
  have hcompare : 24^n≤24*5^(2*n-2) := by
    calc
      24^n=24*24^(n-1) := by
        calc
          24^n=24^((n-1)+1) := congrArg (fun k : ℕ => 24^k) (by omega)
          _=24*24^(n-1) := pow_succ' 24 (n-1)
      _≤24*25^(n-1) := Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left (by decide) (n-1))
      _=24*5^(2*n-2) := by
        rw [show (25:ℕ)=5^2 by decide,←pow_mul]
        exact congrArg (fun k : ℕ => 24*5^k) (by omega)
  exact Nat.le_of_mul_le_mul_left (hscaled.trans hcompare) (by decide)

theorem ternary_gap_of_scaled_cube (n B : ℕ) (hn : 2≤n)
    (hB : 24*B^3≤3^n) : (3^n*B)^3≤5^(3*n-2) := by
  have hbinary := binary_gap_of_scaled_cube n B (by omega) hB
  have hthree : (3^n)^3=27^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have htwo : (2^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have h27 : (3^n)^3≤5^n*(2^n)^3 := by
    rw [hthree,htwo,←mul_pow]
    exact Nat.pow_le_pow_left (by decide : (27:ℕ)≤5*8) n
  calc
    (3^n*B)^3=(3^n)^3*B^3 := mul_pow _ _ _
    _≤(5^n*(2^n)^3)*B^3 := Nat.mul_le_mul_right _ h27
    _=5^n*(2^n*B)^3 := by rw [mul_pow]; ring
    _≤5^n*5^(2*n-2) := Nat.mul_le_mul_left _ hbinary
    _=5^(3*n-2) := by rw [←pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.SmallFibreTwentyFourClassEnvelopeNumerics
