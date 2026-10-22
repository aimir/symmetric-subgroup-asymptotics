import SymmetricSubgroupAsymptotics.CFSGGTwoShortRootVectorActions
import SymmetricSubgroupAsymptotics.CFSGGTwoLongRootVectorActions
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotent
import SymmetricSubgroupAsymptotics.CFSGMatrixFlagNormalizer
import Mathlib.Tactic.LinearCombination

/-! The actual two simple positive units recover the first three
singular prefixes. The test is their full I+X+Y action at parameter one.
The extra fixed direction has nonzero quadratic norm, including in
characteristic two, so no polar-form substitution is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGGTwoSingularPrefix
open CFSGGTwoSerreMatrices CFSGMatrixFlagNormalizer
open CFSGOrthogonalDIndexUnipotent CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

def positivePrefix (k : ℕ) : Submodule K (Index → K) :=
  flagPrefix (K := K) (flagEquiv 4) k

theorem prefix_succ_of_singular_fixed (k : ℕ) (hk : k ≤ 2) (v : Index → K)
    (hvQ : splitQuadraticForm K 4 v = 0)
    (hshort : (rootTransvection K false 0 1 : Mat K) *ᵥ v - v ∈ positivePrefix K k)
    (hlong : (rootTransvection K false 1 1 : Mat K) *ᵥ v - v ∈ positivePrefix K k) :
    v ∈ positivePrefix K (k + 1) := by
  have hnegrow (i : Fin 4) : k ≤ (flagEquiv 4 (neg i)).val := by
    change k ≤ 4 + (Fin.rev i).val
    omega
  have hn0 : v (neg 0) = 0 := by
    have h := hshort (neg 1) (hnegrow 1)
    change (((rootTransvection K false 0 1 : Mat K) *ᵥ v) (neg 1) - v (neg 1)) = 0 at h
    rw [CFSGGTwoShortRootVectorActions.positive_apply] at h
    change (v (neg 1) - 1 * v (neg 0)) - v (neg 1) = 0 at h
    linear_combination -h
  have hn1 : v (neg 1) = 0 := by
    have h := hlong (neg 2) (hnegrow 2)
    change (((rootTransvection K false 1 1 : Mat K) *ᵥ v) (neg 2) - v (neg 2)) = 0 at h
    rw [CFSGGTwoLongRootVectorActions.positive_apply] at h
    change (v (neg 2) - 1 * v (neg 1)) - v (neg 2) = 0 at h
    linear_combination -h
  have hn2 : v (neg 2) = 0 := by
    have h := hshort (pos 3) (by change k ≤ 3; omega)
    change (((rootTransvection K false 0 1 : Mat K) *ᵥ v) (pos 3) - v (pos 3)) = 0 at h
    rw [CFSGGTwoShortRootVectorActions.positive_apply] at h
    change (v (pos 3) - 1 * v (neg 2)) - v (pos 3) = 0 at h
    linear_combination -h
  have hsum : v (pos 3) + v (neg 3) = 0 := by
    have h := hshort (pos 2) (by change k ≤ 2; exact hk)
    change (((rootTransvection K false 0 1 : Mat K) *ᵥ v) (pos 2) - v (pos 2)) = 0 at h
    rw [CFSGGTwoShortRootVectorActions.positive_apply] at h
    change (v (pos 2) + 1 * (v (pos 3) + v (neg 3)) - 1 ^ 2 * v (neg 2)) -
      v (pos 2) = 0 at h
    linear_combination h + hn2
  have hlast : v (pos 3) * v (neg 3) = 0 := by
    rw [splitQuadraticForm_apply] at hvQ
    simpa [splitQ, leftPart, rightPart, dotProduct, Function.comp_apply,
      Fin.sum_univ_succ, hn0, hn1, hn2, pos, neg] using hvQ
  have hp3 : v (pos 3) = 0 := by
    rcases mul_eq_zero.mp hlast with h | h
    · exact h
    · simpa only [h, add_zero] using hsum
  have hn3 : v (neg 3) = 0 := by
    simpa only [hp3, zero_add] using hsum
  have hp1 (hzero : k = 0) : v (pos 1) = 0 := by
    have h := hshort (pos 0) (by change k ≤ 0; omega)
    change (((rootTransvection K false 0 1 : Mat K) *ᵥ v) (pos 0) - v (pos 0)) = 0 at h
    rw [CFSGGTwoShortRootVectorActions.positive_apply] at h
    change (v (pos 0) + 1 * v (pos 1)) - v (pos 0) = 0 at h
    linear_combination h
  have hp2 (hle : k ≤ 1) : v (pos 2) = 0 := by
    have h := hlong (pos 1) (by change k ≤ 1; exact hle)
    change (((rootTransvection K false 1 1 : Mat K) *ᵥ v) (pos 1) - v (pos 1)) = 0 at h
    rw [CFSGGTwoLongRootVectorActions.positive_apply] at h
    change (v (pos 1) + 1 * v (pos 2)) - v (pos 1) = 0 at h
    linear_combination h
  intro x hx
  rcases x with i | i
  · fin_cases i
    · change k + 1 ≤ 0 at hx
      omega
    · exact hp1 (by change k + 1 ≤ 1 at hx; omega)
    · exact hp2 (by change k + 1 ≤ 2 at hx; omega)
    · exact hp3
  · fin_cases i
    · exact hn0
    · exact hn1
    · exact hn2
    · exact hn3

end SymmetricSubgroupAsymptotics.CFSGGTwoSingularPrefix
