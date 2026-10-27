import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformPositiveTables

/-! Uniform literal Cartan weights of the natural primitive family.
The coefficients are actual diagonal entries; no root table is assumed.
Jacobi gives the weight support of every nonzero raising coefficient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformCorootWeights
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformRationalFamily CFSGOrthogonalDUniformGramCoordinates
open CFSGOrthogonalDUniformGramBasis
open CFSGOrthogonalDUniformPositiveProfile CFSGOrthogonalDUniformPositiveTables
variable (r : ℕ) (hr : 4 ≤ r)

def fullWeight (a : Fin r) : BasisIndex r→ℚ
  | .inl _=>0
  | .inr j=>cartan ℚ r a (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
      (CFSGOrthogonalDUniformRootCoordinates.entry r j).1-
    cartan ℚ r a (CFSGOrthogonalDUniformRootCoordinates.entry r j).2
      (CFSGOrthogonalDUniformRootCoordinates.entry r j).2

def weight (a : Fin r) (j : PositiveIndex r) : ℚ := fullWeight r a (fullIndex r j)

theorem cartan_mem (a : Fin r) : Orthogonal r (cartan ℚ r a) :=
  (skewAdjointMatricesLieSubalgebra (gram ℚ r)).lie_mem
    (positive_mem_orthogonal ℚ r a) (negative_mem_orthogonal ℚ r a)

theorem bracket_coordinate (a : Fin r) (M : Mat ℚ r) (j : BasisIndex r) :
    coordinates r hr ⁅cartan ℚ r a,M⁆ j=fullWeight r a j*coordinates r hr M j := by
  obtain ⟨d,hd⟩:=cartan_isDiagonal ℚ r hr a
  cases j with
  | inl i =>
    have hz : diagonal r ⁅cartan ℚ r a,M⁆=0 := by
      funext k
      change (cartan ℚ r a*M-M*cartan ℚ r a) (.inl k) (.inl k)=0
      simp only [hd,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.sub_apply]
      ring
    change CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr
      (diagonal r ⁅cartan ℚ r a,M⁆) i=0*_
    rw [hz,map_zero]
    simp
  | inr j =>
    change (cartan ℚ r a*M-M*cartan ℚ r a)
      (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
      (CFSGOrthogonalDUniformRootCoordinates.entry r j).2=fullWeight r a (.inr j)*
        M (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
          (CFSGOrthogonalDUniformRootCoordinates.entry r j).2
    simp only [fullWeight,hd,Matrix.diagonal_mul,Matrix.mul_diagonal,
      Matrix.sub_apply,Matrix.diagonal_apply_eq]
    ring

include hr in
theorem matrix_weight (a : Fin r) (j : BasisIndex r) :
    ⁅cartan ℚ r a,matrix r j⁆=fullWeight r a j • matrix r j := by
  classical
  rw [←reconstruction r hr _ ((skewAdjointMatricesLieSubalgebra (gram ℚ r)).lie_mem
    (cartan_mem r a) (matrix_mem r j))]
  have hc : coordinates r hr ⁅cartan ℚ r a,matrix r j⁆=
      fullWeight r a j • Pi.single j 1 := by
    funext k
    rw [bracket_coordinate,coordinates_matrix]
    by_cases h : k=j
    · subst k;simp
    · simp [Pi.single_apply,h,Ne.symm h]
  rw [hc,map_smul,Fintype.linearCombination_apply_single,one_smul]

include hr in
theorem positive_matrix_weight (a : Fin r) (j : PositiveIndex r) :
    ⁅cartan ℚ r a,positiveMatrix r j⁆=weight r a j • positiveMatrix r j :=
  matrix_weight r hr a (fullIndex r j)

theorem raising_weight (i a : Fin r) (j k : PositiveIndex r)
    (hc : raising r hr i j k≠0) :
    weight r a k=((CartanMatrix.D r) a i:ℚ)+weight r a j := by
  have hHE : ⁅cartan ℚ r a,positive ℚ r i⁆=
      ((CartanMatrix.D r) a i:ℚ) • positive ℚ r i := by
    simpa only [Int.cast_smul_eq_zsmul] using HE ℚ r hr a i
  have hw : ⁅cartan ℚ r a,⁅positive ℚ r i,positiveMatrix r j⁆⁆=
      (((CartanMatrix.D r) a i:ℚ)+weight r a j) •
        ⁅positive ℚ r i,positiveMatrix r j⁆ := by
    rw [leibniz_lie,hHE,positive_matrix_weight r hr,smul_lie,lie_smul,add_smul]
  have h:=congrArg (fun M : Mat ℚ r=>coordinates r hr M (fullIndex r k)) hw
  simp only [bracket_coordinate,map_smul,Pi.smul_apply,smul_eq_mul] at h
  exact mul_right_cancel₀ hc h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformCorootWeights
