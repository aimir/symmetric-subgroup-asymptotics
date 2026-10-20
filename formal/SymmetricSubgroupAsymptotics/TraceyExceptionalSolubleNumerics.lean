import SymmetricSubgroupAsymptotics.TraceyExceptionalOrbitNumerics
import SymmetricSubgroupAsymptotics.TraceySolublePermutationFormulaRaw

/-! Exact soluble-formula arithmetic for the exceptional odd part three. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem traceyBinaryK_mul {r s : ℕ} (hr : r ≠ 0) (hs : s ≠ 0) :
    traceyBinaryK (r * s) = traceyBinaryK r + traceyBinaryK s := by
  unfold traceyBinaryK
  rw [Nat.factorization_mul hr hs, Finsupp.sum_add_index']
  · intro p
    simp
  · intro p a b
    exact Nat.add_mul a b (p - 1)

theorem traceyBinaryK_three_mul_two_pow (m : ℕ) :
    traceyBinaryK (3 * 2 ^ m) = m + 2 := by
  rw [traceyBinaryK_mul (by decide) (pow_ne_zero _ (by decide)),
    traceyBinaryK_two_pow]
  have hthree : traceyBinaryK 3 = 2 := by
    unfold traceyBinaryK
    rw [(by decide : Nat.Prime 3).factorization]
    simp
  omega

theorem traceySolubleFormula_three_five_sixteenths {m d : ℕ}
    (hs : 24 ≤ 3 * 2 ^ m)
    (h : TraceyBinarySolubleFormulaBounds (3 * 2 ^ m) d) :
    16 * d ≤ 5 * (3 * 2 ^ m) := by
  have hm : 3 ≤ m := by
    by_contra hh
    have hml : m ≤ 2 := by omega
    interval_cases m <;> norm_num at hs
  have hc := binary_middle_le_five_sixteenths (m + 2) (by omega)
  have hh := h.2
  rw [traceyBinaryK_three_mul_two_pow] at hh
  have hp : 0 < 2 ^ (m + 2) := pow_pos (by decide) _
  have hmultiply := Nat.mul_le_mul_left 16 hh
  have hcompare := Nat.mul_le_mul_left (3 * 2 ^ m) hc
  nlinarith

/-- The binary part of an odd multiple of a binary power is exact. -/
theorem tracey_ordProj_odd_mul_two_pow {u : ℕ} (hu : u ≠ 0)
    (hodd : ¬2 ∣ u) (v : ℕ) : ordProj[2] (u * 2 ^ v) = 2 ^ v := by
  rw [Nat.ordProj_mul 2 hu (pow_ne_zero _ (by decide)),
    Nat.ordProj_self_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd hodd]

end SymmetricSubgroupAsymptotics
