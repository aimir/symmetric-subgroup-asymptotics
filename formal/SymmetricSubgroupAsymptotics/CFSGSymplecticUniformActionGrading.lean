import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformRootGrading

/-! Literal ALL-rank simple-root coefficient support, deduced from the
actual diagonal grading and Jacobi. No sparse coefficient table oracle. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformActionGrading
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticUniformRootCoordinates CFSGSymplecticUniformRootGrading
variable (r : ℕ)

theorem negative_weight (i : Fin r) :
    ⁅gradingMatrix r,negative ℚ r i⁆=(-1:ℚ) • negative ℚ r i := by
  by_cases hi : i.val+1<r
  · let next : Fin r:=⟨i.val+1,hi⟩
    let ij : Pair r:=⟨(i,next),by dsimp [next];omega⟩
    have he : negative ℚ r i=matrix ℚ r (.inr (true,.inl ij)) := by
      simp only [negative,positive,dif_pos hi,Matrix.transpose_sub,
        Matrix.transpose_single,matrix,ij,next]
    rw [he,matrix_weight]
    have hg : grade r (.inr (true,.inl ij))= -1 := by
      simp only [grade,entry,ij,diagonalWeight,next,Fin.val_mk,Nat.cast_add,Nat.cast_one]
      ring
    rw [hg]
  · have he : negative ℚ r i=matrix ℚ r (.inr (true,.inr (.inl i))) := by
      simp only [negative,positive,dif_neg hi,Matrix.transpose_single,matrix]
    rw [he,matrix_weight]
    have hr : (r:ℚ)=(i.val:ℚ)+1 := by
      have hn : r=i.val+1:=by omega
      exact_mod_cast hn
    have hg : grade r (.inr (true,.inr (.inl i)))= -1 := by
      simp only [grade,entry,diagonalWeight]
      rw [hr]
      ring
    rw [hg]

private theorem coefficient_support (U : Mat ℚ r) (u : ℚ)
    (hU : ⁅gradingMatrix r,U⁆=u • U) (j k : BasisIndex r)
    (hc : coordinates ℚ r ⁅U,matrix ℚ r j⁆ k≠0) :
    grade r k=u+grade r j := by
  have hw : ⁅gradingMatrix r,⁅U,matrix ℚ r j⁆⁆=
      (u+grade r j) • ⁅U,matrix ℚ r j⁆ := by
    rw [leibniz_lie,hU,matrix_weight,smul_lie,lie_smul,add_smul]
  have h:=congrArg (fun M : Mat ℚ r=>coordinates ℚ r M k) hw
  simp only [bracket_coordinate,map_smul,Pi.smul_apply,smul_eq_mul] at h
  exact mul_right_cancel₀ hc h

theorem raising_support (i : Fin r) (j k : BasisIndex r)
    (hc : coordinates ℚ r ⁅positive ℚ r i,matrix ℚ r j⁆ k≠0) :
    grade r k=1+grade r j :=
  coefficient_support r (positive ℚ r i) 1
    (by simpa only [one_smul] using positive_weight r i) j k hc

theorem lowering_support (i : Fin r) (j k : BasisIndex r)
    (hc : coordinates ℚ r ⁅negative ℚ r i,matrix ℚ r j⁆ k≠0) :
    grade r k=grade r j-1 := by
  have h:=coefficient_support r (negative ℚ r i) (-1) (negative_weight r i) j k hc
  linarith

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformActionGrading
