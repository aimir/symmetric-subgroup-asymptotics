import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformPositiveTables

/-! Uniform literal Cartan weights of the natural primitive family.
The coefficients are actual diagonal entries; no root table is assumed.
Jacobi gives the weight support of every nonzero raising coefficient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformCorootWeights
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticUniformRootCoordinates CFSGSymplecticUniformBlockCoordinates
open CFSGSymplecticUniformBlockLie CFSGSymplecticUniformBlockBasis
open CFSGSymplecticUniformPositiveProfile CFSGSymplecticUniformPositiveTables
variable (r : ℕ)

def fullWeight (a : Fin r) (j : BasisIndex r) : ℚ :=
  cartan ℚ r a (entry r j).1 (entry r j).1-
    cartan ℚ r a (entry r j).2 (entry r j).2

def weight (a : Fin r) (j : PositiveIndex r) : ℚ := fullWeight r a (fullIndex r j)

private theorem positive_mem (i : Fin r) : Block ℚ r (positive ℚ r i) := by
  by_cases hi : i.val+1<r
  · let next : Fin r:=⟨i.val+1,hi⟩
    let ij : Pair r:=⟨(i,next),by dsimp [next];omega⟩
    simpa only [positive,dif_pos hi,matrix,ij,next] using
      matrix_mem ℚ r (.inr (false,.inl ij))
  · simpa only [positive,dif_neg hi,matrix] using
      matrix_mem ℚ r (.inr (false,.inr (.inl i)))

private theorem negative_mem (i : Fin r) : Block ℚ r (negative ℚ r i) := by
  have h:=positive_mem r i
  exact ⟨fun a b=>h.1 b a,fun a b=>h.2.2 b a,fun a b=>h.2.1 b a⟩

theorem cartan_mem (a : Fin r) : Block ℚ r (cartan ℚ r a) :=
  lie_mem ℚ r _ _ (positive_mem r a) (negative_mem r a)

theorem bracket_coordinate (a : Fin r) (M : Mat ℚ r) (j : BasisIndex r) :
    coordinates ℚ r ⁅cartan ℚ r a,M⁆ j=fullWeight r a j*coordinates ℚ r M j := by
  obtain ⟨d,hd⟩:=cartan_isDiagonal ℚ r a
  change (cartan ℚ r a * M - M * cartan ℚ r a)
    (entry r j).1 (entry r j).2 =
      fullWeight r a j * M (entry r j).1 (entry r j).2
  simp only [fullWeight,hd,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.sub_apply,Matrix.diagonal_apply_eq]
  ring

theorem matrix_weight (a : Fin r) (j : BasisIndex r) :
    ⁅cartan ℚ r a,matrix ℚ r j⁆=fullWeight r a j • matrix ℚ r j := by
  classical
  rw [←reconstruction ℚ r _ (lie_mem ℚ r _ _ (cartan_mem r a) (matrix_mem ℚ r j))]
  have hc : coordinates ℚ r ⁅cartan ℚ r a,matrix ℚ r j⁆=
      fullWeight r a j • Pi.single j 1 := by
    funext k
    rw [bracket_coordinate,coordinates_matrix]
    by_cases h : k=j
    · subst k;simp
    · simp [Pi.single_apply,h,Ne.symm h]
  rw [hc,map_smul,Fintype.linearCombination_apply_single,one_smul]

theorem positive_matrix_weight (a : Fin r) (j : PositiveIndex r) :
    ⁅cartan ℚ r a,positiveMatrix r j⁆=weight r a j • positiveMatrix r j :=
  matrix_weight r a (fullIndex r j)

theorem raising_weight (i a : Fin r) (j k : PositiveIndex r)
    (hc : raising r i j k≠0) :
    weight r a k=((CartanMatrix.C r).transpose a i:ℚ)+weight r a j := by
  have hHE : ⁅cartan ℚ r a,positive ℚ r i⁆=
      ((CartanMatrix.C r).transpose a i:ℚ) • positive ℚ r i := by
    simpa only [typeC_transpose,Int.cast_smul_eq_zsmul] using HE (R:=ℚ) r a i
  have hw : ⁅cartan ℚ r a,⁅positive ℚ r i,positiveMatrix r j⁆⁆=
      (((CartanMatrix.C r).transpose a i:ℚ)+weight r a j) •
        ⁅positive ℚ r i,positiveMatrix r j⁆ := by
    rw [leibniz_lie,hHE,positive_matrix_weight,smul_lie,lie_smul,add_smul]
  have h:=congrArg (fun M : Mat ℚ r=>coordinates ℚ r M (fullIndex r k)) hw
  simp only [bracket_coordinate,map_smul,Pi.smul_apply,smul_eq_mul] at h
  exact mul_right_cancel₀ hc h

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformCorootWeights
