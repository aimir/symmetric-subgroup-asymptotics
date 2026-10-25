import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! Multiple alternating socle factors need only the coarse partition
bound2^m. The degree retains BOTH b>=4096 and m^k<=b; no equality of the
original proper index with m is assumed. This is purely integer algebra. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AlternatingMultiFactorSmallFibreClassNumerics

private theorem exponent_le_power (m : ℕ) (hm : 5 ≤ m) (k : ℕ) (hk : 3 ≤ k) :
    3 * (k * m + 3 * k + k * k) + 2 ≤ m ^ k := by
  induction k,hk using Nat.le_induction with
  | base =>
    have hsq : 25 ≤ m * m := Nat.mul_le_mul hm hm
    have hcube : 25 * m ≤ m ^ 3 := by
      simpa only [pow_succ,pow_zero,Nat.one_mul,Nat.mul_assoc] using
        Nat.mul_le_mul_right m hsq
    nlinarith only [hm,hcube]
  | succ k hk ih =>
    have hkm : 3 * m ≤ k * m := Nat.mul_le_mul_right m hk
    have hs : 3 * ((k + 1) * m + 3 * (k + 1) + (k + 1) * (k + 1)) + 2 ≤
        2 * (3 * (k * m + 3 * k + k * k) + 2) := by
      nlinarith only [hm,hk,hkm,Nat.zero_le (k * k)]
    exact hs.trans ((Nat.mul_le_mul_left 2 ih).trans
      ((Nat.mul_le_mul_right (m ^ k) (by omega : 2 ≤ m)).trans_eq
        (by rw [pow_succ,Nat.mul_comm])))

theorem exponent_budget (m k b : ℕ) (hm : 5 ≤ m) (hk : 2 ≤ k)
    (hb : 4096 ≤ b) (hdegree : m ^ k ≤ b) :
    3 * (k * m + 3 * k + k * k) + 2 ≤ b := by
  by_cases hthree : 3 ≤ k
  · exact (exponent_le_power m hm k hthree).trans hdegree
  have hk2 : k = 2 := by omega
  subst k
  by_cases hm10 : 10 ≤ m
  · have hmul : 10 * m ≤ m * m := Nat.mul_le_mul_right m hm10
    have hsq : 6 * m + 32 ≤ m ^ 2 := by nlinarith only [hm10,hmul]
    nlinarith only [hsq,hdegree]
  · have hm9 : m ≤ 9 := by omega
    nlinarith only [hm9,hb]

private theorem factorial_le_binary_square (k : ℕ) : k.factorial ≤ 2 ^ (k * k) := by
  exact (Nat.factorial_le_pow k).trans
    ((Nat.pow_le_pow_left k.lt_two_pow_self.le k).trans_eq (pow_mul 2 k k).symm)

private theorem envelope_le (m k : ℕ) :
    (8 * 2 ^ m) ^ k * k.factorial ≤ 2 ^ (k * m + 3 * k + k * k) := by
  calc
    (8 * 2 ^ m) ^ k * k.factorial ≤ (8 * 2 ^ m) ^ k * 2 ^ (k * k) :=
      Nat.mul_le_mul_left _ (factorial_le_binary_square k)
    _ = 2 ^ ((3 + m) * k + k * k) := by
      rw [show (8 : ℕ) = 2 ^ 3 by decide,← pow_add,← pow_mul,← pow_add]
    _ = 2 ^ (k * m + 3 * k + k * k) := by congr 1; ring

theorem binary_product_cube_le (m k b : ℕ) (hm : 5 ≤ m) (hk : 2 ≤ k)
    (hb : 4096 ≤ b) (hdegree : m ^ k ≤ b) :
    (2 ^ b * ((8 * 2 ^ m) ^ k * k.factorial)) ^ 3 ≤ 5 ^ (2 * b - 1) := by
  have he : (b + (k * m + 3 * k + k * k)) * 3 ≤ 2 * (2 * b - 1) := by
    have h := exponent_budget m k b hm hk hb hdegree
    omega
  calc
    (2 ^ b * ((8 * 2 ^ m) ^ k * k.factorial)) ^ 3 ≤
        (2 ^ b * 2 ^ (k * m + 3 * k + k * k)) ^ 3 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (envelope_le m k)) 3
    _ = 2 ^ ((b + (k * m + 3 * k + k * k)) * 3) := by rw [← pow_add,← pow_mul]
    _ ≤ 2 ^ (2 * (2 * b - 1)) := Nat.pow_le_pow_right (by decide) he
    _ = 4 ^ (2 * b - 1) := by rw [show (4 : ℕ) = 2 ^ 2 by decide,pow_mul]
    _ ≤ 5 ^ (2 * b - 1) := Nat.pow_le_pow_left (by decide) _

theorem ternary_product_cube_le (m k b : ℕ) (hm : 5 ≤ m) (hk : 2 ≤ k)
    (hb : 4096 ≤ b) (hdegree : m ^ k ≤ b) :
    (3 ^ b * ((8 * 2 ^ m) ^ k * k.factorial)) ^ 3 ≤ 5 ^ (3 * b - 1) := by
  have hbinary := binary_product_cube_le m k b hm hk hb hdegree
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
    _ = 5 ^ b * (2 ^ b * ((8 * 2 ^ m) ^ k * k.factorial)) ^ 3 := by
      rw [mul_pow]; ring
    _ ≤ 5 ^ b * 5 ^ (2 * b - 1) := Nat.mul_le_mul_left _ hbinary
    _ = 5 ^ (3 * b - 1) := by rw [← pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.AlternatingMultiFactorSmallFibreClassNumerics
