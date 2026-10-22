import SymmetricSubgroupAsymptotics.CFSGTwistedDForkPositiveAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotent
import SymmetricSubgroupAsymptotics.CFSGMatrixFlagNormalizer
import Mathlib.Tactic.LinearCombination

/-! Actual chain tests and the full paired-fork word recover the same
singular prefixes through rank r-1 in every field. The last fixed pair
is excluded by Q itself, including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPrefix
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDForkPositiveAction CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexBundledQuadratic CFSGMatrixFlagNormalizer
open CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

def positivePrefix (s k : ℕ) : Submodule K (Index (s + 2) → K) :=
  flagPrefix (K := K) (flagEquiv (s + 2)) k

def chainNode (s : ℕ) (i : Fin s) : Fin (s + 2) := ⟨i.val, by have := i.isLt; omega⟩

theorem prefix_succ_of_singular_fixed (s k : ℕ) (hk : k ≤ s) (v : Index (s + 2) → K)
    (hvQ : splitQuadraticForm K (s + 2) v = 0)
    (hchain : ∀ i : Fin s,
      (rootTransvection K (s + 2) false (chainNode s i) 1 : Mat K (s + 2)) *ᵥ v - v ∈
        positivePrefix K s k)
    (hfold : (foldedFork K s : Mat K (s + 2)) *ᵥ v - v ∈ positivePrefix K s k) :
    v ∈ positivePrefix K s (k + 1) := by
  have hnegrow (j : Fin (s + 2)) : k ≤ (flagEquiv (s + 2) (Sum.inr j)).val := by
    change k ≤ s + 2 + (Fin.rev j).val
    omega
  have hnpen : v (Sum.inr (pen s)) = 0 := by
    have h := hfold (Sum.inr (last s)) (hnegrow _)
    change ((foldedFork K s : Mat K (s + 2)) *ᵥ v) (Sum.inr (last s)) -
      v (Sum.inr (last s)) = 0 at h
    rw [foldedFork_mulVec] at h
    have he : (v (Sum.inr (last s)) - v (Sum.inr (pen s))) - v (Sum.inr (last s)) = 0 := by
      simpa [Pi.add_apply, Pi.sub_apply, pen_ne_last s, Ne.symm (pen_ne_last s)] using h
    linear_combination -he
  have hneg (j : Fin (s + 2)) (hj : j ≠ last s) : v (Sum.inr j) = 0 := by
    by_cases hjp : j = pen s
    · simpa only [hjp] using hnpen
    have hval : j.val < s := by
      have hb := j.isLt
      have ha : j.val ≠ s + 1 := fun h => hj (Fin.ext (by simpa [last] using h))
      have hc : j.val ≠ s := fun h => hjp (Fin.ext (by simpa [pen] using h))
      omega
    let i : Fin s := ⟨j.val, hval⟩
    have hnode : chainNode s i = j := Fin.ext rfl
    have hi : (chainNode s i).val + 1 < s + 2 := by dsimp [chainNode, i]; omega
    have h := hchain i (Sum.inr (⟨(chainNode s i).val + 1, hi⟩ : Fin (s + 2))) (hnegrow _)
    change ((rootTransvection K (s + 2) false (chainNode s i) 1 : Mat K (s + 2)) *ᵥ v)
      (Sum.inr (⟨(chainNode s i).val + 1, hi⟩ : Fin (s + 2))) -
      v (Sum.inr (⟨(chainNode s i).val + 1, hi⟩ : Fin (s + 2))) = 0 at h
    rw [chain_negative_action K _ hi] at h
    have hz : v (Sum.inr (chainNode s i)) = 0 := by linear_combination -h
    simpa only [hnode] using hz
  have hsum : v (Sum.inl (last s)) + v (Sum.inr (last s)) = 0 := by
    have h := hfold (Sum.inl (pen s)) (by change k ≤ s; exact hk)
    change ((foldedFork K s : Mat K (s + 2)) *ᵥ v) (Sum.inl (pen s)) -
      v (Sum.inl (pen s)) = 0 at h
    rw [foldedFork_mulVec] at h
    have he : ((v (Sum.inl (pen s)) + v (Sum.inl (last s))) + v (Sum.inr (last s)) -
        v (Sum.inr (pen s))) - v (Sum.inl (pen s)) = 0 := by
      simpa [Pi.add_apply, Pi.sub_apply, pen_ne_last s, Ne.symm (pen_ne_last s)] using h
    linear_combination he + hnpen
  have hlast : v (Sum.inl (last s)) * v (Sum.inr (last s)) = 0 := by
    rw [splitQuadraticForm_apply] at hvQ
    change (∑ j : Fin (s + 2), v (Sum.inl j) * v (Sum.inr j)) = 0 at hvQ
    have he : (∑ j : Fin (s + 2), v (Sum.inl j) * v (Sum.inr j)) =
        v (Sum.inl (last s)) * v (Sum.inr (last s)) := by
      apply Finset.sum_eq_single (last s)
      · intro j _ hj
        rw [hneg j hj, mul_zero]
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    rwa [he] at hvQ
  have hplast : v (Sum.inl (last s)) = 0 := by
    rcases mul_eq_zero.mp hlast with h | h
    · exact h
    · simpa only [h, add_zero] using hsum
  have hnlast : v (Sum.inr (last s)) = 0 := by
    simpa only [hplast, zero_add] using hsum
  intro x hx
  cases x with
  | inr j =>
    by_cases hj : j = last s
    · simpa only [hj] using hnlast
    · exact hneg j hj
  | inl j =>
    by_cases hj : j = last s
    · simpa only [hj] using hplast
    have hjb := j.isLt
    have hjl : j.val ≠ s + 1 := fun h => hj (Fin.ext (by simpa [last] using h))
    change k + 1 ≤ j.val at hx
    let i : Fin s := ⟨j.val - 1, by omega⟩
    have hi : (chainNode s i).val + 1 < s + 2 := by dsimp [chainNode, i]; omega
    have hnext : (⟨(chainNode s i).val + 1, hi⟩ : Fin (s + 2)) = j := by
      apply Fin.ext
      dsimp [chainNode, i]
      omega
    have h := hchain i (Sum.inl (chainNode s i)) (by
      change k ≤ (chainNode s i).val
      dsimp [chainNode, i]
      omega)
    change ((rootTransvection K (s + 2) false (chainNode s i) 1 : Mat K (s + 2)) *ᵥ v)
      (Sum.inl (chainNode s i)) - v (Sum.inl (chainNode s i)) = 0 at h
    rw [chain_positive_action K _ hi] at h
    have hz : v (Sum.inl (⟨(chainNode s i).val + 1, hi⟩ : Fin (s + 2))) = 0 := by
      linear_combination h
    simpa only [hnext] using hz

end SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPrefix
