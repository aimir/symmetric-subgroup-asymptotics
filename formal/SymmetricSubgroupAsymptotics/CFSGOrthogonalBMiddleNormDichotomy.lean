import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNonzeroMiddleCommonNeighbour
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
import Mathlib.Tactic.LinearCombination

/-! The SAME original Gram norm leaves exactly two middle-normalized
vectors once their paired projections share one scalar. No projective
recognition or field-size estimate is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleNormDichotomy
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSingularVectorCount CFSGOrthogonalBNonzeroMiddleCommonNeighbour
variable (K : Type) [Field K]

theorem projections_ne_zero (n : ℕ) (v : Index n → K)
    (hv : (gram K n).toBilin' v v = 0) (hm : v (middle n) = 1) :
    positivePart K n v ≠ 0 ∧ negativePart K n v ≠ 0 := by
  constructor
  · intro hz
    rw [gram_norm_dot, hz] at hv
    simp [CFSGParabolicQuadricCount.dotDual, hm] at hv
  · intro hz
    rw [gram_norm_dot, hz] at hv
    simp [CFSGParabolicQuadricCount.dotDual, hm] at hv

theorem eq_or_antipode_of_paired_scalar (n : ℕ) (v y : Index n → K)
    (hv : (gram K n).toBilin' v v = 0) (hy : (gram K n).toBilin' y y = 0)
    (hvm : v (middle n) = 1) (hym : y (middle n) = 1) (c : K)
    (hp : positivePart K n y = c • positivePart K n v)
    (hn : negativePart K n y = c • negativePart K n v) :
    y = v ∨ y = antipode K n v := by
  have hd : CFSGParabolicQuadricCount.dotDual (fun i => 4 * positivePart K n y i)
      (negativePart K n y) = c ^ 2 *
        CFSGParabolicQuadricCount.dotDual (fun i => 4 * positivePart K n v i)
          (negativePart K n v) := by
    rw [hp, hn]
    change (∑ i : Fin n, 4 * (c * positivePart K n v i) *
      (c * negativePart K n v i)) =
      c ^ 2 * ∑ i : Fin n, 4 * positivePart K n v i * negativePart K n v i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [gram_norm_dot, hvm, one_pow] at hv
  rw [gram_norm_dot, hym, one_pow, hd] at hy
  have hc : c ^ 2 = 1 := by linear_combination c ^ 2 * hv - hy
  rcases sq_eq_one_iff.mp hc with hc | hc
  · left
    rw [hc, one_smul] at hp hn
    funext i
    rcases i with (i | i) | ⟨⟩
    · exact congrFun hp i
    · exact congrFun hn i
    · exact hym.trans hvm.symm
  · right
    rw [hc, neg_one_smul] at hp hn
    funext i
    rcases i with (i | i) | ⟨⟩
    · change y (pos n i) = (2 : K) * 0 - v (pos n i)
      simpa only [mul_zero, zero_sub] using congrFun hp i
    · change y (neg n i) = (2 : K) * 0 - v (neg n i)
      simpa only [mul_zero, zero_sub] using congrFun hn i
    · change y (middle n) = (2 : K) * 1 - v (middle n)
      rw [hym, hvm]
      ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleNormDichotomy
