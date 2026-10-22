import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexParameters
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootLines
import SymmetricSubgroupAsymptotics.CFSGMatrixShearUnits
import Mathlib.Data.Matrix.Basis

/-! Every parameterized alternating upper/lower block shear belongs to
the original elementary D group. Membership is proved additively from
actual root lines, without dividing by two or assuming full orthogonal
recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexShears
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexParameters
open CFSGOrthogonalDIndexRootLines CFSGOrthogonalDIndexTranspose CFSGMatrixShearUnits
open CFSGOrthogonalDGenerationRootArrays CFSGOrthogonalDGenerationRootLineSymmetries
variable (K : Type) [Field K]

private theorem upper_pair_val (s : ℕ) (i j : Fin (s + 4)) (a : K) :
    (upper (Matrix.single i j a - Matrix.single j i a) : Mat K (s + 4)) = plusArray i j a := by
  ext x y
  cases x <;> cases y <;>
    simp [upper, Matrix.fromBlocks, plusArray, Matrix.one_apply,
      Matrix.single_apply, Matrix.add_apply, Matrix.sub_apply]

private theorem upper_pair_mem (s : ℕ) (i j : Fin (s + 4)) (hij : i ≠ j) (a : K) :
    upper (Matrix.single i j a - Matrix.single j i a) ∈ elementaryRootGroup K (s + 4) :=
  unit_mem_of_line K _ _ (plus_line K s i j hij) _ a (upper_pair_val K s i j a)

theorem alternating_sum {r : ℕ} (p : Parameters K r) :
    alternating p = ∑ i, ∑ j,
      (Matrix.single i j (strictUpper p i j) - Matrix.single j i (strictUpper p i j)) := by
  simp only [Finset.sum_sub_distrib]
  rw [Matrix.sum_sum_single]
  unfold alternating
  congr 1
  have ht := congrArg Matrix.transpose (Matrix.sum_sum_single (strictUpper p))
  simpa only [Matrix.transpose_sum, Matrix.transpose_single] using ht.symm

theorem upper_alternating_mem (s : ℕ) (p : Parameters K (s + 4)) :
    upper (alternating p) ∈ elementaryRootGroup K (s + 4) := by
  let P := upperParameters (elementaryRootGroup K (s + 4))
  change alternating p ∈ P
  rw [alternating_sum]
  apply P.sum_mem
  intro i _
  apply P.sum_mem
  intro j _
  by_cases hij : i.val < j.val
  · exact upper_pair_mem K s i j (fun he => (Nat.ne_of_lt hij) (congrArg Fin.val he)) _
  · simp only [strictUpper, dif_neg hij, Matrix.single_zero, sub_zero]
    exact P.zero_mem

theorem lower_alternating_mem (s : ℕ) (p : Parameters K (s + 4)) :
    lower (alternating p) ∈ elementaryRootGroup K (s + 4) := by
  have hu := (elementaryRootGroup K (s + 4)).inv_mem (upper_alternating_mem K s p)
  have ht := transposeUnit_mem K (s + 4) _ hu
  have he : transposeUnit K (s + 4) (upper (alternating p))⁻¹ = lower (alternating p) := by
    apply Units.ext
    change (Matrix.fromBlocks (1 : Matrix (Fin (s + 4)) (Fin (s + 4)) K)
      (-alternating p) 0 1).transpose = Matrix.fromBlocks 1 0 (alternating p) 1
    simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.transpose_neg, alternating_transpose, neg_neg]
  exact he ▸ ht

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexShears
