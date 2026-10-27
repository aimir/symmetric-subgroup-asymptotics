import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanGrading

/-! Positive comparison for the actual original-D induction. The grading
is a positive combination of the simple Cartan images; cancellation uses the nonzero
root vectors separately, never a possibly-zero raising bracket. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveComparison
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformRationalFamily CFSGOrthogonalDUniformRootGrading
open CFSGOrthogonalDUniformPositiveProfile CFSGOrthogonalDUniformPositiveTables
open CFSGOrthogonalDUniformCorootWeights CFSGOrthogonalDCartanGrading
variable (r : ℕ) (hr : 4 ≤ r)

def charge (w : Fin r→ℚ) : ℚ := ∑ i : Fin r,coefficient r hr i*w i

private theorem charge_eigen (M : Mat ℚ r) (w : Fin r→ℚ)
    (hw : ∀ a,⁅cartan ℚ r a,M⁆=w a • M) :
    ⁅gradingMatrix r,M⁆=charge r hr w • M := by
  rw [grading_cartan_sum r hr,sum_lie]
  simp_rw [smul_lie,hw,smul_smul]
  rw [←Finset.sum_smul]
  rfl

private theorem charge_eq (M : Mat ℚ r) (hM : M≠0) (w : Fin r → ℚ) (mu : ℚ)
    (hw : ∀ a,⁅cartan ℚ r a,M⁆=w a • M)
    (hZ : ⁅gradingMatrix r,M⁆=mu • M) : charge r hr w=mu := by
  classical
  obtain ⟨x,y,hxy⟩ : ∃ x y,M x y≠0 := by
    by_contra h
    push_neg at h
    exact hM (Matrix.ext fun x y=>h x y)
  have h := congrArg (fun N : Mat ℚ r=>N x y) ((charge_eigen r hr M w hw).symm.trans hZ)
  exact mul_right_cancel₀ hxy h

private theorem charge_nonpos (w : Fin r→ℚ) (hw : ∀ a,w a≤0) :
    charge r hr w≤0 := by
  apply Finset.sum_nonpos
  intro i hi
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (coefficient_pos r hr i)) (hw i)

include hr in
private theorem positive_ne_zero (i : Fin r) : positive ℚ r i≠0 := by
  intro hz
  by_cases hi : i.val+1 < r
  · let next : Fin r:=⟨i.val+1,hi⟩
    have h:=congrArg (fun M : Mat ℚ r=>M (.inl i) (.inl next)) hz
    simpa [positive,hi,next,Matrix.single_apply] using h
  · let prev:=previous r i
    have hp : prev≠i := by
      intro he
      have hh:=congrArg Fin.val he
      have hil:=i.isLt
      dsimp [prev,previous] at hh
      omega
    have h:=congrArg (fun M : Mat ℚ r=>M (.inl prev) (.inr i)) hz
    simpa [positive,hi,prev,Matrix.single_apply,hp,Ne.symm hp] using h

include hr in
theorem positive_comparison (i : Fin r) (j : PositiveIndex r) :
    ∃ a,0 < ((CartanMatrix.D r) a i:ℚ)+weight r a j := by
  classical
  have hE : charge r hr (fun a=>((CartanMatrix.D r) a i:ℚ))=1 :=
    charge_eq r hr _ (positive_ne_zero r hr i) _ 1
      (fun a=>by simpa only [Int.cast_smul_eq_zsmul] using HE ℚ r hr a i)
      (by simpa only [one_smul] using positive_weight r hr i)
  have hM : positiveMatrix r j≠0 := by
    intro hz
    have h:=congrArg (fun M : Mat ℚ r=>coordinates r hr M (fullIndex r j)) hz
    simpa only [positiveMatrix,coordinates_matrix,map_zero,Pi.single_eq_same,Pi.zero_apply,one_ne_zero] using h
  have hJ : charge r hr (fun a=>weight r a j)=(height r j:ℚ) := by
    apply charge_eq r hr _ hM _ _ (fun a=>positive_matrix_weight r hr a j)
    simpa only [positiveMatrix,fullIndex_grade] using
      CFSGOrthogonalDUniformRootGrading.matrix_weight r hr (fullIndex r j)
  by_contra h
  push_neg at h
  have hn:=charge_nonpos r hr (fun a=>((CartanMatrix.D r) a i:ℚ)+weight r a j) h
  have hadd : charge r hr (fun a=>((CartanMatrix.D r) a i:ℚ)+weight r a j)=
      charge r hr (fun a=>((CartanMatrix.D r) a i:ℚ))+charge r hr (fun a=>weight r a j) := by
    simp only [charge,Finset.sum_add_distrib,mul_add]
  rw [hadd,hE,hJ] at hn
  have hnonneg : (0:ℚ)≤(height r j:ℚ) := Nat.cast_nonneg _
  linarith

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveComparison
