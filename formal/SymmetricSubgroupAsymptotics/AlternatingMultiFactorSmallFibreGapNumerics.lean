import SymmetricSubgroupAsymptotics.AlternatingMultiFactorSmallFibreClassNumerics

/-! A one-exponent reserve for several actual alternating socle
factors. The original m^k<=b degree inequality and b>=4096 are retained;
the earlier exponent certificate is reused unchanged. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AlternatingMultiFactorSmallFibreGapNumerics

private theorem four_pow_succ_le_five_pow (m : ℕ) (hm : 7 ≤ m) :
    4 ^ (m + 1) ≤ 5 ^ m := by
  induction m,hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    calc
      4 ^ (m + 1 + 1) = 4 ^ (m + 1) * 4 := pow_succ _ _
      _ ≤ 5 ^ m * 5 := Nat.mul_le_mul ih (by decide)
      _ = 5 ^ (m + 1) := (pow_succ _ _).symm

private theorem envelope_le (m k : ℕ) :
    (8 * 2 ^ m) ^ k * k.factorial ≤ 2 ^ (k * m + 3 * k + k * k) := by
  have hf : k.factorial ≤ 2 ^ (k * k) :=
    (Nat.factorial_le_pow k).trans
      ((Nat.pow_le_pow_left k.lt_two_pow_self.le k).trans_eq (pow_mul 2 k k).symm)
  calc
    (8 * 2 ^ m) ^ k * k.factorial ≤ (8 * 2 ^ m) ^ k * 2 ^ (k * k) :=
      Nat.mul_le_mul_left _ hf
    _ = 2 ^ ((3 + m) * k + k * k) := by
      rw [show (8 : ℕ) = 2 ^ 3 by decide,← pow_add,← pow_mul,← pow_add]
    _ = 2 ^ (k * m + 3 * k + k * k) := by congr 1; ring

theorem binary_product_cube_gap (m k b : ℕ) (hm : 5 ≤ m) (hk : 2 ≤ k)
    (hb : 4096 ≤ b) (hdegree : m ^ k ≤ b) :
    (2 ^ b * ((8 * 2 ^ m) ^ k * k.factorial)) ^ 3 ≤ 5 ^ (2 * b - 2) := by
  have he : (b + (k * m + 3 * k + k * k)) * 3 ≤ 2 * (2 * b - 1) := by
    have h := AlternatingMultiFactorSmallFibreClassNumerics.exponent_budget m k b hm hk hb hdegree
    omega
  have hfour : 4 ^ (2 * b - 1) ≤ 5 ^ (2 * b - 2) := by
    have h : 2 * b - 1 = (2 * b - 2) + 1 := by omega
    rw [h]
    exact four_pow_succ_le_five_pow _ (by omega)
  calc
    (2 ^ b * ((8 * 2 ^ m) ^ k * k.factorial)) ^ 3 ≤
        (2 ^ b * 2 ^ (k * m + 3 * k + k * k)) ^ 3 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (envelope_le m k)) 3
    _ = 2 ^ ((b + (k * m + 3 * k + k * k)) * 3) := by rw [← pow_add,← pow_mul]
    _ ≤ 2 ^ (2 * (2 * b - 1)) := Nat.pow_le_pow_right (by decide) he
    _ = 4 ^ (2 * b - 1) := by rw [show (4 : ℕ) = 2 ^ 2 by decide,pow_mul]
    _ ≤ 5 ^ (2 * b - 2) := hfour

theorem ternary_product_cube_gap (m k b : ℕ) (hm : 5 ≤ m) (hk : 2 ≤ k)
    (hb : 4096 ≤ b) (hdegree : m ^ k ≤ b) :
    (3 ^ b * ((8 * 2 ^ m) ^ k * k.factorial)) ^ 3 ≤ 5 ^ (3 * b - 2) := by
  have hbinary := binary_product_cube_gap m k b hm hk hb hdegree
  have hthree : (3 ^ b) ^ 3 = 27 ^ b := by
    rw [← pow_mul,Nat.mul_comm b 3,pow_mul]
    norm_num
  have htwo : (2 ^ b) ^ 3 = 8 ^ b := by
    rw [← pow_mul,Nat.mul_comm b 3,pow_mul]
    norm_num
  have h27 : (3 ^ b) ^ 3 ≤ 5 ^ b * (2 ^ b) ^ 3 := by
    rw [hthree,htwo,← mul_pow]
    exact Nat.pow_le_pow_left (by decide : 27 ≤ 5 * 8) b
  calc
    (3 ^ b * ((8 * 2 ^ m) ^ k * k.factorial)) ^ 3 =
        (3 ^ b) ^ 3 * ((8 * 2 ^ m) ^ k * k.factorial) ^ 3 := mul_pow _ _ _
    _ ≤ (5 ^ b * (2 ^ b) ^ 3) * ((8 * 2 ^ m) ^ k * k.factorial) ^ 3 :=
      Nat.mul_le_mul_right _ h27
    _ = 5 ^ b * (2 ^ b * ((8 * 2 ^ m) ^ k * k.factorial)) ^ 3 := by rw [mul_pow]; ring
    _ ≤ 5 ^ b * 5 ^ (2 * b - 2) := Nat.mul_le_mul_left _ hbinary
    _ = 5 ^ (3 * b - 2) := by rw [← pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.AlternatingMultiFactorSmallFibreGapNumerics
