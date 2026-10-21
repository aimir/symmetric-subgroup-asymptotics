import SymmetricSubgroupAsymptotics.CFSGSquareZeroAdjoint
import SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Divided adjoint powers of square-zero target roots have integral
formulas. Consequently they preserve every actual subring containing the
root, despite being initially defined by rational factorial denominators. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSquareZeroDividedPowers
variable {B : Type*} [Ring B] [Algebra ℚ B]

def operator (e : B) (k : ℕ) : Module.End ℚ B :=
  (k.factorial : ℚ)⁻¹ • (LieAlgebra.ad ℚ B e ^ k)

@[simp] theorem operator_zero (e x : B) : operator e 0 x = x := by
  simp [operator]

@[simp] theorem operator_one (e x : B) : operator e 1 x = ⁅e, x⁆ := by
  simp [operator]

theorem operator_two (e x : B) (he : e * e = 0) : operator e 2 x = -(e * x * e) := by
  change (2 : ℚ)⁻¹ • ⁅e, ⁅e, x⁆⁆ = _
  rw [CFSGSquareZeroAdjoint.lie_lie e x he, ← two_smul ℚ (e * x * e), smul_neg, smul_smul]
  norm_num

theorem operator_large (e x : B) (he : e * e = 0) (k : ℕ) (hk : 3 ≤ k) :
    operator e k x = 0 := by
  have h3 : (LieAlgebra.ad ℚ B e ^ 3) x = 0 := by
    change ⁅e, ⁅e, ⁅e, x⁆⁆⁆ = 0
    exact CFSGSquareZeroAdjoint.lie_lie_lie e x he
  change (k.factorial : ℚ)⁻¹ • ((LieAlgebra.ad ℚ B e ^ k) x) = 0
  rw [CFSGSerreLocalNilpotence.end_pow_apply_zero_of_le _ h3 hk, smul_zero]

theorem operator_mem_subring (T : Subring B) (e : B) (he : e ∈ T) (hee : e * e = 0)
    (k : ℕ) (x : B) (hx : x ∈ T) : operator e k x ∈ T := by
  by_cases hk : 3 ≤ k
  · rw [operator_large e x hee k hk]
    exact T.zero_mem
  · have hlt : k < 3 := by omega
    interval_cases k
    · simpa only [operator_zero] using hx
    · rw [operator_one]
      change e * x - x * e ∈ T
      exact T.sub_mem (T.mul_mem he hx) (T.mul_mem hx he)
    · rw [operator_two e x hee]
      exact T.neg_mem (T.mul_mem (T.mul_mem he hx) he)

end SymmetricSubgroupAsymptotics.CFSGSquareZeroDividedPowers
