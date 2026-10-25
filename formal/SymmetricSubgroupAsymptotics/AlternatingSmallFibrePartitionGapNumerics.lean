import SymmetricSubgroupAsymptotics.AlternatingSmallFibrePartitionTailNumerics

/-! One additional exponent of saving in the separated-cut partition
envelope. The checked five-step ratio is reused unchanged; a stronger
single coarse seed reserves the extra power for an outer small top. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.AlternatingSmallFibrePartitionGapNumerics
open AlternatingSmallFibrePartitionTailNumerics

private theorem envelope_cube_blocks_gap (q : ℕ) (hq : 819 ≤ q) (r : ℕ) (hr : r < 5) :
    envelope (5 * q + r) ^ 3 ≤ 5 ^ (2 * (5 * q + r) - 2) := by
  induction q,hq using Nat.le_induction with
  | base =>
    have hexp : 8188 ≤ 2 * (5 * 819 + r) - 2 := by omega
    have hsmall : 5 * 819 + r ≤ 4099 := by omega
    have hseed : envelope 4099 ^ 3 ≤ 5 ^ 8188 := by decide +kernel
    have hh := (Nat.pow_le_pow_left (envelope_mono hsmall) 3).trans hseed
    exact hh.trans (Nat.pow_le_pow_right (by decide : 0 < (5 : ℕ)) hexp)
  | succ q hq ih =>
    have hn : 199 ≤ 5 * q + r := by omega
    have he : 5 * (q + 1) + r = (5 * q + r) + 5 := by omega
    calc
      envelope (5 * (q + 1) + r) ^ 3 = envelope ((5 * q + r) + 5) ^ 3 := by rw [he]
      _ ≤ 5 ^ 10 * envelope (5 * q + r) ^ 3 := envelope_cube_step _ hn
      _ ≤ 5 ^ 10 * 5 ^ (2 * (5 * q + r) - 2) := Nat.mul_le_mul_left _ ih
      _ = 5 ^ (2 * (5 * (q + 1) + r) - 2) := by rw [← pow_add]; congr 1; omega

theorem binary_partition_envelope_cube_gap (n : ℕ) (hn : 4096 ≤ n) :
    (2 ^ n * 8 * (n + 1) ^ 4 * 6 ^ ((n + 4) / 5)) ^ 3 ≤ 5 ^ (2 * n - 2) := by
  have hq : 819 ≤ n / 5 := by omega
  have hr : n % 5 < 5 := Nat.mod_lt n (by decide)
  have he : 5 * (n / 5) + n % 5 = n := by omega
  simpa only [he,envelope] using envelope_cube_blocks_gap (n / 5) hq (n % 5) hr

theorem ternary_partition_envelope_cube_gap (n : ℕ) (hn : 4096 ≤ n) :
    (3 ^ n * 8 * (n + 1) ^ 4 * 6 ^ ((n + 4) / 5)) ^ 3 ≤ 5 ^ (3 * n - 2) := by
  let T : ℕ := 8 * (n + 1) ^ 4 * 6 ^ ((n + 4) / 5)
  have hb : (2 ^ n * T) ^ 3 ≤ 5 ^ (2 * n - 2) := by
    simpa only [T,Nat.mul_assoc] using binary_partition_envelope_cube_gap n hn
  have h3 : ((3 : ℕ) ^ n) ^ 3 = 27 ^ n := by
    rw [← pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have h2 : ((2 : ℕ) ^ n) ^ 3 = 8 ^ n := by
    rw [← pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have hfinal : (3 ^ n * T) ^ 3 ≤ 5 ^ (3 * n - 2) := by
    calc
      (3 ^ n * T) ^ 3 = 27 ^ n * T ^ 3 := by rw [mul_pow,h3]
      _ ≤ 40 ^ n * T ^ 3 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) n)
      _ = (2 ^ n * T) ^ 3 * 5 ^ n := by
        rw [show (40 : ℕ) = 8 * 5 by decide,mul_pow]
        conv_rhs => rw [mul_pow,h2]
        ring
      _ ≤ 5 ^ (2 * n - 2) * 5 ^ n := Nat.mul_le_mul_right _ hb
      _ = 5 ^ (3 * n - 2) := by rw [← pow_add]; congr 1; omega
  simpa only [T,Nat.mul_assoc] using hfinal

end SymmetricSubgroupAsymptotics.AlternatingSmallFibrePartitionGapNumerics
