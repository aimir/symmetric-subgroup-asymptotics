import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotent
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveCentralizer
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticShears

/-! Actual paired positive-root test elements in D-unipotent U, and
the first intrinsic centre reduction. Every central U matrix is an
upper shear with zero diagonal and skew paired coefficients, including
characteristic two. No C diagonal-long root is inserted into D. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveRoots
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveCentralizer CFSGOrthogonalDIndexQuadraticShears
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexRootLines CFSGMatrixShearUnits
open CFSGOrthogonalDGenerationRootArrays CFSGOrthogonalDGenerationRootLineSymmetries
variable (K : Type) [Field K]

private theorem pair_upper_val (s : ℕ) (i j : Fin (s + 4)) (a : K) :
    (upper (Matrix.single i j a - Matrix.single j i a) : Mat K (s + 4)) = plusArray i j a := by
  ext x y
  cases x <;> cases y <;>
    simp [upper, Matrix.fromBlocks, plusArray, Matrix.one_apply,
      Matrix.single_apply, Matrix.add_apply, Matrix.sub_apply]

def pairInU (s : ℕ) (i j : Fin (s + 4)) (hij : i ≠ j) (a : K) : unipotent K (s + 4) :=
  ⟨⟨upper (Matrix.single i j a - Matrix.single j i a),
    unit_mem_of_line K _ _ (plus_line K s i j hij) _ a (pair_upper_val K s i j a)⟩,
    upperShear_triangular K (s + 4) _, by intro x; cases x <;> exact Matrix.one_apply_eq _⟩

theorem pairInU_val (s : ℕ) (i j : Fin (s + 4)) (hij : i ≠ j) (a : K) :
    ((pairInU K s i j hij a).val.val : Mat K (s + 4)) = 1 + a • pairedUpper K i j := by
  change (upper (Matrix.single i j a - Matrix.single j i a) : Mat K (s + 4)) = _
  rw [pair_upper_val]
  simp only [pairedUpper, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, plusArray]
  abel

theorem central_unipotent_is_upper_shear (s : ℕ) (z : unipotent K (s + 4))
    (hz : z ∈ Subgroup.center (unipotent K (s + 4))) :
    (z.val.val : Mat K (s + 4)) =
      Matrix.fromBlocks 1 ((z.val.val : Mat K (s + 4)).submatrix Sum.inl Sum.inr) 0 1 := by
  apply upper_of_paired_commutation K s _ (unipotent_lower_left_zero K (s + 4) z) z.property.2
  intro i j hij
  have h := congrArg (fun v : unipotent K (s + 4) => (v.val.val : Mat K (s + 4)))
    ((Subgroup.mem_center_iff.mp hz) (pairInU K s i j hij 1)).symm
  change (z.val.val : Mat K (s + 4)) * ((pairInU K s i j hij 1).val.val : Mat K (s + 4)) =
    ((pairInU K s i j hij 1).val.val : Mat K (s + 4)) * (z.val.val : Mat K (s + 4)) at h
  rw [pairInU_val, one_smul] at h
  simp only [mul_add, add_mul, mul_one, one_mul] at h
  exact add_left_cancel h

theorem central_unipotent_upper_alternating (s : ℕ) (z : unipotent K (s + 4))
    (hz : z ∈ Subgroup.center (unipotent K (s + 4))) :
    ∀ i j : Fin (s + 4),
      (z.val.val : Mat K (s + 4)) (Sum.inl i) (Sum.inr i) = 0 ∧
      (z.val.val : Mat K (s + 4)) (Sum.inl i) (Sum.inr j) +
        (z.val.val : Mat K (s + 4)) (Sum.inl j) (Sum.inr i) = 0 := by
  let B := (z.val.val : Mat K (s + 4)).submatrix Sum.inl Sum.inr
  have hQ : ∀ x : Index (s + 4) → K, splitQ K ((upper B : Mat K (s + 4)) *ᵥ x) = splitQ K x := by
    intro x
    have h := elementary_preserves_splitQ K s z.val x
    rw [central_unipotent_is_upper_shear K s z hz] at h
    exact h
  intro i j
  exact ⟨upper_diagonal_zero_of_preserves_splitQ K B hQ i,
    upper_pair_sum_zero_of_preserves_splitQ K B hQ i j⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveRoots
