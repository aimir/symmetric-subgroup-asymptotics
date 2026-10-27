import SymmetricSubgroupAsymptotics.CFSGSymplecticCartanTailGrading

/-! Positive comparison for the actual original-C induction. The grading
is a positive combination of Cartan tails; cancellation uses the nonzero
root vectors separately, never a possibly-zero raising bracket. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPositiveComparison
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticUniformRootCoordinates CFSGSymplecticUniformRootGrading
open CFSGSymplecticUniformPositiveProfile CFSGSymplecticUniformPositiveTables
open CFSGSymplecticUniformCorootWeights CFSGSymplecticCartanTailGrading
variable (r : ℕ)

def weightAt (w : Fin r → ℚ) (a : ℕ) : ℚ :=
  if h : a < r then w ⟨a,h⟩ else 0

def charge (w : Fin r → ℚ) : ℚ :=
  ∑ i : Fin r,coefficient r i * ∑ a ∈ Finset.range (r-i.val),weightAt r w (i.val+a)

private theorem charge_eigen (M : Mat ℚ r) (w : Fin r → ℚ)
    (hw : ∀ a,⁅cartan ℚ r a,M⁆=w a • M) :
    ⁅gradingMatrix r,M⁆=charge r w • M := by
  have ha : ∀ a,⁅cartanAt r a,M⁆=weightAt r w a • M := by
    intro a
    unfold cartanAt weightAt
    split_ifs with h
    · exact hw ⟨a,h⟩
    · simp
  rw [grading_tail_sum,sum_lie]
  simp_rw [smul_lie,sum_lie,ha]
  simp_rw [←Finset.sum_smul,smul_smul]
  rw [←Finset.sum_smul]
  rfl

private theorem charge_eq (M : Mat ℚ r) (hM : M≠0) (w : Fin r → ℚ) (mu : ℚ)
    (hw : ∀ a,⁅cartan ℚ r a,M⁆=w a • M)
    (hZ : ⁅gradingMatrix r,M⁆=mu • M) : charge r w=mu := by
  classical
  obtain ⟨x,y,hxy⟩ : ∃ x y,M x y≠0 := by
    by_contra h
    push_neg at h
    exact hM (Matrix.ext fun x y=>h x y)
  have h := congrArg (fun N : Mat ℚ r=>N x y) ((charge_eigen r M w hw).symm.trans hZ)
  exact mul_right_cancel₀ hxy h

private theorem charge_nonpos (w : Fin r → ℚ) (hw : ∀ a,w a≤0) :
    charge r w≤0 := by
  apply Finset.sum_nonpos
  intro i hi
  apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt (coefficient_pos r i))
  apply Finset.sum_nonpos
  intro a ha
  unfold weightAt
  split_ifs with h
  · exact hw ⟨i.val+a,h⟩
  · rfl

private theorem positive_ne_zero (i : Fin r) : positive ℚ r i≠0 := by
  intro hz
  by_cases hi : i.val+1 < r
  · let next : Fin r:=⟨i.val+1,hi⟩
    have h:=congrArg (fun M : Mat ℚ r=>M (.inl i) (.inl next)) hz
    simpa [positive,hi,next,Matrix.single_apply] using h
  · have h:=congrArg (fun M : Mat ℚ r=>M (.inl i) (.inr i)) hz
    simpa [positive,hi,Matrix.single_apply] using h

theorem positive_comparison (i : Fin r) (j : PositiveIndex r) :
    ∃ a,0 < ((CartanMatrix.C r).transpose a i:ℚ)+weight r a j := by
  classical
  have hE : charge r (fun a=>((CartanMatrix.C r).transpose a i:ℚ))=1 :=
    charge_eq r _ (positive_ne_zero r i) _ 1
      (fun a=>by simpa only [typeC_transpose,Int.cast_smul_eq_zsmul] using HE (R:=ℚ) r a i)
      (by simpa only [one_smul] using positive_weight r i)
  have hM : positiveMatrix r j≠0 := by
    intro hz
    have h:=congrArg (fun M : Mat ℚ r=>coordinates ℚ r M (fullIndex r j)) hz
    simpa only [positiveMatrix,coordinates_matrix,map_zero,Pi.single_eq_same,Pi.zero_apply,one_ne_zero] using h
  have hJ : charge r (fun a=>weight r a j)=(height r j:ℚ) := by
    apply charge_eq r _ hM _ _ (fun a=>positive_matrix_weight r a j)
    cases j with
    | inl b =>
      have h:=CFSGSymplecticUniformRootGrading.matrix_weight r (.inl b)
      simpa [positiveMatrix,fullIndex,grade,entry,height] using h
    | inr b =>
      simpa only [positiveMatrix,fullIndex,positive_root_grade,height] using
        CFSGSymplecticUniformRootGrading.matrix_weight r (.inr (false,b))
  by_contra h
  push_neg at h
  have hn:=charge_nonpos r (fun a=>((CartanMatrix.C r).transpose a i:ℚ)+weight r a j) h
  have hadd : charge r (fun a=>((CartanMatrix.C r).transpose a i:ℚ)+weight r a j)=
      charge r (fun a=>((CartanMatrix.C r).transpose a i:ℚ))+charge r (fun a=>weight r a j) := by
    have hat : ∀ a,weightAt r (fun a=>((CartanMatrix.C r).transpose a i:ℚ)+weight r a j) a=
        weightAt r (fun a=>((CartanMatrix.C r).transpose a i:ℚ)) a+
          weightAt r (fun a=>weight r a j) a := by
      intro a
      unfold weightAt
      split_ifs <;> simp
    simp only [charge,hat,Finset.sum_add_distrib,mul_add]
  rw [hadd,hE,hJ] at hn
  have hnonneg : (0:ℚ)≤(height r j:ℚ) := Nat.cast_nonneg _
  linarith

end SymmetricSubgroupAsymptotics.CFSGSymplecticPositiveComparison
