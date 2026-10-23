import SymmetricSubgroupAsymptotics.CFSGBlockTriangularColumn
import SymmetricSubgroupAsymptotics.CFSGFinitePermutationOrder

/-! Bruhat block permutations are unique, even with a nontrivial Cartan
block. Only actual invertibility, triangular support and block-permutation
support are used. No Bruhat uniqueness theorem is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGBlockMonomialBruhatUniqueness
open CFSGBlockTriangularColumn
variable {I L K : Type*} [Fintype I] [DecidableEq I] [LinearOrder L] [Field K]

theorem block_permutation_le (weight : I → L)
    (A B W1 W2 : (Matrix I I K)ˣ)
    (hA : (A : Matrix I I K).BlockTriangular weight)
    (hB : (B : Matrix I I K).BlockTriangular weight)
    (phi1 phi2 : Equiv.Perm L)
    (hW1 : ∀ i j, weight i ≠ phi1 (weight j) → (W1 : Matrix I I K) i j = 0)
    (hW2 : ∀ i j, weight i ≠ phi2 (weight j) → (W2 : Matrix I I K) i j = 0)
    (hM : W2 * A = B * W1) (j : I) : phi2 (weight j) ≤ phi1 (weight j) := by
  classical
  let v := blockColumn weight (A : Matrix I I K) j
  have hv : v ≠ 0 := blockColumn_nonzero weight A hA j
  have hvW : (W2 : Matrix I I K) *ᵥ v ≠ 0 := by
    intro hz
    apply hv
    apply Matrix.mulVec_injective_of_isUnit W2.isUnit
    exact hz.trans (Matrix.mulVec_zero _).symm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hvW
  have hi0 : ((W2 : Matrix I I K) *ᵥ v) i ≠ 0 := hi
  have hweight : weight i = phi2 (weight j) := by
    by_contra hn
    apply hi0
    change (∑ k, (W2 : Matrix I I K) i k * v k) = 0
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : weight k = weight j
    · rw [hW2 i k (by simpa only [hk] using hn), zero_mul]
    · rw [show v k = 0 by simp only [v, blockColumn, if_neg hk], mul_zero]
  have hcut : ((W2 : Matrix I I K) * (A : Matrix I I K)) i j =
      ((W2 : Matrix I I K) *ᵥ v) i := by
    change (∑ k, (W2 : Matrix I I K) i k * (A : Matrix I I K) k j) =
      ∑ k, (W2 : Matrix I I K) i k * v k
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : weight k = weight j
    · rw [show v k = (A : Matrix I I K) k j by simp only [v, blockColumn, if_pos hk]]
    · have hn : weight i ≠ phi2 (weight k) := by
        rw [hweight]
        exact fun h => hk (phi2.injective h.symm)
      rw [hW2 i k hn, zero_mul, zero_mul]
  apply le_of_not_gt
  intro hlt
  have hright : ((B : Matrix I I K) * (W1 : Matrix I I K)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : weight k = phi1 (weight j)
    · rw [hB (by rw [hk, hweight]; exact hlt), zero_mul]
    · rw [hW1 k j hk, mul_zero]
  have hm := congrArg (fun U : (Matrix I I K)ˣ => (U : Matrix I I K) i j) hM
  exact hi0 (hcut.symm.trans (hm.trans hright))

theorem block_bruhat_permutation_unique [Fintype L] (weight : I → L)
    (hweight : Function.Surjective weight)
    (B1 B2 W1 W2 : (Matrix I I K)ˣ)
    (hB1 : (B1 : Matrix I I K).BlockTriangular weight)
    (hB2 : (B2 : Matrix I I K).BlockTriangular weight)
    (phi1 phi2 : Equiv.Perm L)
    (hW1 : ∀ i j, weight i ≠ phi1 (weight j) → (W1 : Matrix I I K) i j = 0)
    (hW2 : ∀ i j, weight i ≠ phi2 (weight j) → (W2 : Matrix I I K) i j = 0)
    (hM : B1 * W1 * B2 = W2) : phi1 = phi2 := by
  have he : W2 * B2⁻¹ = B1 * W1 := by
    rw [← hM, mul_assoc, mul_inv_cancel, mul_one]
  have hle (l : L) : phi2 l ≤ phi1 l := by
    obtain ⟨j, rfl⟩ := hweight l
    exact block_permutation_le weight B2⁻¹ B1 W1 W2
      (inverse_upper weight B2 hB2) hB1 phi1 phi2 hW1 hW2 he j
  exact (CFSGFinitePermutationOrder.eq_of_pointwise_le phi2 phi1 hle).symm

end SymmetricSubgroupAsymptotics.CFSGBlockMonomialBruhatUniqueness
