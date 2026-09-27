import SymmetricSubgroupAsymptotics.MarkerPairFactorial
import Mathlib.Data.Real.Basic

/-! The exact merged-pair occurrence ratio is bounded by the falling
factorial used by the complete normalized marker kernel. The old pair
count remains in the denominator until this monotonicity step. -/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.MarkerMergedFactorial

theorem ratio_eq_descFactorial (p q : ℕ) :
    ((p + q).factorial : ℚ) / (p.factorial : ℚ) =
      ((p + q).descFactorial q : ℚ) := by
  rw [MarkerPairFactorial.ratio_eq_rising, Nat.add_descFactorial_eq_ascFactorial]

theorem ratio_le_descFactorial (p q M : ℕ) (hM : p + q ≤ M) :
    ((p + q).factorial : ℚ) / (p.factorial : ℚ) ≤ (M.descFactorial q : ℚ) := by
  rw [ratio_eq_descFactorial]
  exact_mod_cast Nat.descFactorial_le q hM

theorem ratio_le_descFactorial_real (p q M : ℕ) (hM : p + q ≤ M) :
    ((p + q).factorial : ℝ) / (p.factorial : ℝ) ≤ (M.descFactorial q : ℝ) := by
  have hr : ((p + q).factorial : ℝ) / (p.factorial : ℝ) =
      ((p + q).descFactorial q : ℝ) := by
    apply (div_eq_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p))).mpr
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (Nat.factorial_mul_descFactorial (n := p + q) (k := q) (by omega))
    simpa only [Nat.add_sub_cancel_right, Nat.cast_mul, mul_comm] using h.symm
  rw [hr]
  exact_mod_cast Nat.descFactorial_le q hM

end SymmetricSubgroupAsymptotics.MarkerMergedFactorial
