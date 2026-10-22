import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveChains
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexFlagVectors

/-! The simultaneous fixed space of the SAME D flag-unipotent group
is exactly its first natural line in every characteristic. All tests
are actual positive chain/paired root elements of that subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotentFixedSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveRoots CFSGOrthogonalDIndexPositiveChains
open CFSGOrthogonalDIndexFlagVectors CFSGOrthogonalDGenerationRootArrays
variable (K : Type) [Field K]

private theorem single_mulVec {r : ℕ} (i j : Index r) (a : K) (x : Index r → K) :
    Matrix.single i j a *ᵥ x = Pi.single i (a * x j) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · have hik : i ≠ k := Ne.symm hk
    simp [Matrix.mulVec, dotProduct, hk, hik]

theorem fixed_space_first_line (s : ℕ) (x : Index (s + 4) → K)
    (hx : ∀ u : unipotent K (s + 4), (u.val.val : Mat K (s + 4)) *ᵥ x = x) :
    x = x (Sum.inl 0) • firstVector K s := by
  have hpos (j : Fin (s + 4)) (hj : j ≠ 0) : x (Sum.inl j) = 0 := by
    have hlt : (0 : Fin (s + 4)) < j := by
      change 0 < j.val
      have hn : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega
    have h := hx (chainInU K (s + 4) 0 j hlt 1)
    change ((chainElement K (s + 4) 0 j _ 1).val : Mat K (s + 4)) *ᵥ x = x at h
    rw [chainElement_val] at h
    have he := congrFun h (Sum.inl 0)
    simp only [chainArray, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      single_mulVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply, one_mul] at he
    have hh : x (Sum.inl 0) + x (Sum.inl j) = x (Sum.inl 0) := by simpa using he
    exact add_left_cancel (hh.trans (add_zero _).symm)
  have hneg0 : x (Sum.inr (0 : Fin (s + 4))) = 0 := by
    have h := hx (chainInU K (s + 4) 0 (secondIndex s)
      (by change (0 : Fin (s + 4)).val < (1 : Fin (s + 4)).val
          simp only [Fin.val_zero, Fin.val_one]
          omega) 1)
    change ((chainElement K (s + 4) 0 (secondIndex s) _ 1).val : Mat K (s + 4)) *ᵥ x = x at h
    rw [chainElement_val] at h
    have he := congrFun h (Sum.inr (secondIndex s))
    simp only [chainArray, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      single_mulVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply, one_mul] at he
    have hh : x (Sum.inr (secondIndex s)) - x (Sum.inr 0) = x (Sum.inr (secondIndex s)) := by
      simpa using he
    linear_combination -hh
  have hneg (j : Fin (s + 4)) (hj : j ≠ 0) : x (Sum.inr j) = 0 := by
    have h := hx (pairInU K s 0 j (Ne.symm hj) 1)
    rw [pairInU_val, one_smul] at h
    change (1 + (Matrix.single (Sum.inl 0) (Sum.inr j) 1 -
      Matrix.single (Sum.inl j) (Sum.inr 0) 1)) *ᵥ x = x at h
    have he := congrFun h (Sum.inl 0)
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      single_mulVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply, one_mul] at he
    have hh : x (Sum.inl 0) + x (Sum.inr j) = x (Sum.inl 0) := by
      simpa [hj, Ne.symm hj] using he
    exact add_left_cancel (hh.trans (add_zero _).symm)
  funext i
  cases i with
  | inl j =>
    by_cases hj : j = 0
    · subst j
      simp [firstVector]
    · simp [firstVector, hj, hpos j hj]
  | inr j =>
    by_cases hj : j = 0
    · subst j
      simp [firstVector, hneg0]
    · simp [firstVector, hneg j hj]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotentFixedSpace
