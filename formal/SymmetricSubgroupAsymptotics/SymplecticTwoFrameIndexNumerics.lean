import SymmetricSubgroupAsymptotics.SymplecticEvenHigherSiegelNumerics

/-! Arithmetic consequences of the same-annihilator two-frame numerator.
The field-two specialization keeps its exact half-numerator; the other
fields use one uniform power lower bound. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SymplecticTwoFrameIndexNumerics
open SymplecticEvenHigherSiegelNumerics

theorem field_four_power_le (q r n : ℕ) (hq : 4 ≤ q) (hr : 3 ≤ r)
    (h : (q-1)*q^(r-2)*(q^r-q) ≤ 2*n) : q^(2*r-2) ≤ n := by
  have hpow : 3*q ≤ q^r := by
    have hq2 : 3*q ≤ q^2 := by nlinarith
    exact hq2.trans (Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 2 ≤ r))
  have hinner : 2*q^r ≤ (q-1)*(q^r-q) := by
    have hh : 2*q^r ≤ 3*(q^r-q) := by omega
    exact hh.trans (Nat.mul_le_mul_right _ (by omega : 3 ≤ q-1))
  have hexp : q^(2*r-2) = q^(r-2)*q^r := by
    rw [← pow_add]
    congr 1
    omega
  have hlo : 2*q^(2*r-2) ≤ (q-1)*q^(r-2)*(q^r-q) := by
    rw [hexp]
    calc
      2*(q^(r-2)*q^r) = q^(r-2)*(2*q^r) := by ring
      _ ≤ q^(r-2)*((q-1)*(q^r-q)) := Nat.mul_le_mul_left _ hinner
      _ = (q-1)*q^(r-2)*(q^r-q) := by ring
  omega

theorem binary_power_le (r n : ℕ) (hr : 3 ≤ r)
    (h : (2-1)*2^(r-2)*(2^r-2) ≤ 2*n) : binaryIndexLower r ≤ n := by
  have he : r-2 = (r-3)+1 := by omega
  have hn : (2-1)*2^(r-2)*(2^r-2) = 2*binaryIndexLower r := by
    unfold binaryIndexLower
    rw [he, pow_succ]
    norm_num only [Nat.reduceSub, one_mul]
    ring
  rw [hn] at h
  omega

theorem field_four_power_ge_thirtyTwo (q r : ℕ) (hq : 4 ≤ q) (hr : 3 ≤ r) :
    32 ≤ q^(2*r-2) := by
  exact ((by decide : 32 ≤ (4 : ℕ)^4).trans
    (Nat.pow_le_pow_left hq 4)).trans
    (Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 4 ≤ 2*r-2))

theorem binary_ge_thirtyTwo (r : ℕ) (hr : 5 ≤ r) : 32 ≤ binaryIndexLower r := by
  exact ((by decide : 32 ≤ (2 : ℕ)^6).trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 6 ≤ 2*r-4))).trans
    (binary_index_ge_power r hr)

end SymmetricSubgroupAsymptotics.SymplecticTwoFrameIndexNumerics
