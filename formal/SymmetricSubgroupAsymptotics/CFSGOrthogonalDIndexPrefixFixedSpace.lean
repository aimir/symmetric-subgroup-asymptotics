import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveChains
import SymmetricSubgroupAsymptotics.CFSGMatrixFlagNormalizer

/-! The actual D-unipotent action recovers successive positive flag
prefixes up to dimension r-1. The final two coordinates are deliberately
not separated: the missing central-pair root is not a D root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixFixedSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveRoots CFSGOrthogonalDIndexPositiveChains
open CFSGOrthogonalDGenerationRootArrays CFSGOrthogonalDIndexPositiveCentralizer
open CFSGMatrixFlagNormalizer
variable (K : Type) [Field K]

private theorem single_mulVec {r : ℕ} (i j : Index r) (a : K) (x : Index r → K) :
    Matrix.single i j a *ᵥ x = Pi.single i (a * x j) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · have hik : i ≠ k := Ne.symm hk
    simp [Matrix.mulVec, dotProduct, hk, hik]

theorem prefix_succ_fixed (s k : ℕ) (v : Index (s + 4) → K)
    (hv : v ∈ flagPrefix (K := K) (flagEquiv (s + 4)) (k + 1)) :
    ∀ u : unipotent K (s + 4),
      (u.val.val : Mat K (s + 4)) *ᵥ v - v ∈
        flagPrefix (K := K) (flagEquiv (s + 4)) k := by
  intro u i hi
  have he : ((u.val.val : Mat K (s + 4)) *ᵥ v) i = v i := by
    change (∑ j, (u.val.val : Mat K (s + 4)) i j * v j) = v i
    calc
      _ = (u.val.val : Mat K (s + 4)) i i * v i := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          have hne : flagEquiv (s + 4) j ≠ flagEquiv (s + 4) i :=
            (flagEquiv (s + 4)).injective.ne hji
          rcases lt_or_gt_of_ne hne with hj | hj
          · have hz := u.property.1 hj
            change (u.val.val : Mat K (s + 4)) i j = 0 at hz
            rw [hz, zero_mul]
          · have hz : v j = 0 := hv j (by
              change (flagEquiv (s + 4) i).val < (flagEquiv (s + 4) j).val at hj
              omega)
            rw [hz, mul_zero]
        · intro hni
          exact False.elim (hni (Finset.mem_univ i))
      _ = v i := by
        have hd := u.property.2 i
        change (u.val.val : Mat K (s + 4)) i i = 1 at hd
        rw [hd, one_mul]
  change ((u.val.val : Mat K (s + 4)) *ᵥ v) i - v i = 0
  rw [he, sub_self]

theorem prefix_succ_of_fixed (s k : ℕ) (hk : k + 1 < s + 4)
    (v : Index (s + 4) → K)
    (hv : ∀ u : unipotent K (s + 4),
      (u.val.val : Mat K (s + 4)) *ᵥ v - v ∈
        flagPrefix (K := K) (flagEquiv (s + 4)) k) :
    v ∈ flagPrefix (K := K) (flagEquiv (s + 4)) (k + 1) := by
  let i : Fin (s + 4) := ⟨k, by omega⟩
  let next : Fin (s + 4) := ⟨k + 1, hk⟩
  have hrow : k ≤ (flagEquiv (s + 4) (Sum.inl i)).val := by
    change k ≤ k
    exact le_rfl
  have hnegrow (j : Fin (s + 4)) :
      k ≤ (flagEquiv (s + 4) (Sum.inr j)).val := by
    change k ≤ s + 4 + (Fin.rev j).val
    omega
  have hpos (j : Fin (s + 4)) (hj : k < j.val) : v (Sum.inl j) = 0 := by
    have hij : i < j := by change k < j.val; exact hj
    have he := hv (chainInU K (s + 4) i j hij 1) (Sum.inl i) hrow
    change (((chainElement K (s + 4) i j _ 1).val : Mat K (s + 4)) *ᵥ v - v)
      (Sum.inl i) = 0 at he
    rw [chainElement_val] at he
    simp [chainArray, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      single_mulVec] at he
    linear_combination he
  have hnegi : v (Sum.inr i) = 0 := by
    have hin : i < next := by change k < k + 1; omega
    have he := hv (chainInU K (s + 4) i next hin 1) (Sum.inr next) (hnegrow next)
    change (((chainElement K (s + 4) i next _ 1).val : Mat K (s + 4)) *ᵥ v - v)
      (Sum.inr next) = 0 at he
    rw [chainElement_val] at he
    simp [chainArray, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      single_mulVec] at he
    exact he
  have hneg (j : Fin (s + 4)) : v (Sum.inr j) = 0 := by
    by_cases hji : j = i
    · simpa only [hji] using hnegi
    · have he := hv (pairInU K s i j (Ne.symm hji) 1) (Sum.inl i) hrow
      rw [pairInU_val, one_smul] at he
      simp [pairedUpper, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        single_mulVec, Ne.symm hji] at he
      linear_combination he
  intro x hx
  cases x with
  | inl j =>
    apply hpos j
    change k + 1 ≤ j.val at hx
    omega
  | inr j => exact hneg j

theorem prefix_succ_iff_fixed (s k : ℕ) (hk : k + 1 < s + 4)
    (v : Index (s + 4) → K) :
    v ∈ flagPrefix (K := K) (flagEquiv (s + 4)) (k + 1) ↔
      ∀ u : unipotent K (s + 4),
        (u.val.val : Mat K (s + 4)) *ᵥ v - v ∈
          flagPrefix (K := K) (flagEquiv (s + 4)) k :=
  ⟨prefix_succ_fixed K s k v, prefix_succ_of_fixed K s k hk v⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixFixedSpace
