import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootGrading

/-! Genuine D raising/lowering coefficient support, from the literal
natural grading and Jacobi, without a rank-dependent root-table oracle. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformActionGrading
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformRationalFamily CFSGOrthogonalDUniformRootGrading
variable (r : ℕ) (hr : 4 ≤ r)

include hr in
theorem negative_weight (i : Fin r) :
    ⁅gradingMatrix r,negative ℚ r i⁆=(-1:ℚ) • negative ℚ r i := by
  have h:=congrArg Matrix.transpose (positive_weight r hr i)
  have h' : negative ℚ r i*gradingMatrix r-gradingMatrix r*negative ℚ r i=negative ℚ r i := by
    simpa only [Ring.lie_def,Matrix.transpose_sub,Matrix.transpose_mul,
      gradingMatrix,Matrix.diagonal_transpose,negative] using h
  change gradingMatrix r*negative ℚ r i-negative ℚ r i*gradingMatrix r=(-1:ℚ) • negative ℚ r i
  rw [neg_one_smul]
  simpa only [neg_sub] using congrArg Neg.neg h'

private theorem coefficient_support (U : Mat ℚ r) (u : ℚ)
    (hU : ⁅gradingMatrix r,U⁆=u • U) (j k : BasisIndex r)
    (hc : coordinates r hr ⁅U,matrix r j⁆ k≠0) :
    grade r k=u+grade r j := by
  have hw : ⁅gradingMatrix r,⁅U,matrix r j⁆⁆=(u+grade r j) • ⁅U,matrix r j⁆ := by
    rw [leibniz_lie,hU,matrix_weight r hr,smul_lie,lie_smul,add_smul]
  have h:=congrArg (fun M : Mat ℚ r=>coordinates r hr M k) hw
  simp only [bracket_coordinate,map_smul,Pi.smul_apply,smul_eq_mul] at h
  exact mul_right_cancel₀ hc h

theorem raising_support (i : Fin r) (j k : BasisIndex r)
    (hc : coordinates r hr ⁅positive ℚ r i,matrix r j⁆ k≠0) : grade r k=1+grade r j :=
  coefficient_support r hr _ 1 (by simpa only [one_smul] using positive_weight r hr i) j k hc

theorem lowering_support (i : Fin r) (j k : BasisIndex r)
    (hc : coordinates r hr ⁅negative ℚ r i,matrix r j⁆ k≠0) : grade r k=grade r j-1 := by
  have h:=coefficient_support r hr _ (-1) (negative_weight r hr i) j k hc
  linarith

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformActionGrading
