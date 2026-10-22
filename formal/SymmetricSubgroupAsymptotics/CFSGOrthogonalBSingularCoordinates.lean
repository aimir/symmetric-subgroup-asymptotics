import SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRationalForm
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Exact original odd-dimensional Gram norm in positive/negative/middle
coordinates. No quadratic-form isomorphism or counting assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSerreMatrices
variable (K : Type) [Field K]

theorem gram_norm_coordinates (n : ℕ) (v : Index n → K) :
    (gram K n).toBilin' v v =
      (∑ i : Fin n, (positivePart K n v i * 2 * negativePart K n v i +
        negativePart K n v i * 2 * positivePart K n v i)) + v (middle n) ^ 2 := by
  simp [Matrix.toBilin'_apply, gram, Fintype.sum_sum_type, positivePart, negativePart,
    pos, neg, middle, Finset.sum_add_distrib, mul_ite, ite_mul, pow_two]
  exact add_comm _ _

theorem gram_norm_positive_basis (n : ℕ) (v : Index (n + 1) → K)
    (hv : positivePart K (n + 1) v = Pi.single 0 1) :
    (gram K (n + 1)).toBilin' v v =
      4 * v (neg (n + 1) 0) + v (middle (n + 1)) ^ 2 := by
  rw [gram_norm_coordinates, hv]
  simp [Pi.single_apply, Finset.sum_add_distrib, mul_ite, ite_mul, negativePart]
  ring

theorem positive_or_negative_nonzero (n : ℕ) (v : Index n → K) (hv : v ≠ 0)
    (hs : (gram K n).toBilin' v v = 0) :
    positivePart K n v ≠ 0 ∨ negativePart K n v ≠ 0 := by
  by_cases hp : positivePart K n v = 0
  · right
    intro hn
    have hm : v (middle n) ^ 2 = 0 := by
      rw [gram_norm_coordinates, hp, hn] at hs
      simpa only [Pi.zero_apply, zero_mul, add_zero, Finset.sum_const_zero, zero_add] using hs
    have hm0 : v (middle n) = 0 := sq_eq_zero_iff.mp hm
    apply hv
    funext x
    rcases x with (i | i) | ⟨⟩
    · exact congrFun hp i
    · exact congrFun hn i
    · exact hm0
  · exact Or.inl hp

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
