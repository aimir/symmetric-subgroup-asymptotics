import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankRootLines
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexShears

/-! The original alternating shear membership theorem extended to the
actual rank-two and rank-three D tails using proved all-rank root lines.
No low-rank matrix/model correspondence is inserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankShears
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexParameters
open CFSGOrthogonalDIndexAllRankRootLines CFSGOrthogonalDIndexTranspose
open CFSGOrthogonalDIndexShears CFSGMatrixShearUnits
open CFSGOrthogonalDGenerationRootArrays CFSGOrthogonalDGenerationRootLineSymmetries
variable (K : Type) [Field K]

theorem upper_pair_val {r : ℕ} (i j : Fin r) (a : K) :
    (upper (Matrix.single i j a - Matrix.single j i a) : Mat K r) = plusArray i j a := by
  ext x y
  cases x <;> cases y <;>
    simp [upper, Matrix.fromBlocks, plusArray, Matrix.one_apply,
      Matrix.single_apply, Matrix.add_apply, Matrix.sub_apply]

theorem upper_pair_mem (r : ℕ) (hr : 2 ≤ r) (i j : Fin r) (hij : i ≠ j) (a : K) :
    upper (Matrix.single i j a - Matrix.single j i a) ∈ elementaryRootGroup K r :=
  unit_mem_of_line K _ _ (plus_line_all_ranks K r hr i j hij) _ a (upper_pair_val K i j a)

theorem upper_alternating_mem_all_ranks (r : ℕ) (hr : 2 ≤ r) (p : Parameters K r) :
    upper (alternating p) ∈ elementaryRootGroup K r := by
  let P := upperParameters (elementaryRootGroup K r)
  change alternating p ∈ P
  rw [alternating_sum]
  apply P.sum_mem
  intro i _
  apply P.sum_mem
  intro j _
  by_cases hij : i.val < j.val
  · exact upper_pair_mem K r hr i j (fun he => (Nat.ne_of_lt hij) (congrArg Fin.val he)) _
  · simp only [strictUpper, dif_neg hij, Matrix.single_zero, sub_zero]
    exact P.zero_mem

theorem lower_alternating_mem_all_ranks (r : ℕ) (hr : 2 ≤ r) (p : Parameters K r) :
    lower (alternating p) ∈ elementaryRootGroup K r := by
  have hu := (elementaryRootGroup K r).inv_mem (upper_alternating_mem_all_ranks K r hr p)
  have ht := transposeUnit_mem K r _ hu
  have he : transposeUnit K r (upper (alternating p))⁻¹ = lower (alternating p) := by
    apply Units.ext
    change (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K)
      (-alternating p) 0 1).transpose = Matrix.fromBlocks 1 0 (alternating p) 1
    simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.transpose_neg, alternating_transpose, neg_neg]
  exact he ▸ ht

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankShears
