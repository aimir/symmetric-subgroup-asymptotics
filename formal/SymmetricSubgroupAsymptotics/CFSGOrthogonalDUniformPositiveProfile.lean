import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootGrading

/-! Actual D positive-root heights agree with the diagonal grading.
The fork-root path order is retained in the height expression. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformPositiveProfile
open CFSGOrthogonalDOriginalRootCandidates CFSGOrthogonalDUniformRootGrading
variable (r : ℕ)
abbrev PositiveIndex := Fin r ⊕ RootIndex r

def fullIndex : PositiveIndex r→BasisIndex r
  | .inl i=>.inl i
  | .inr j=>.inr (false,j)

def rootHeight : RootIndex r→ℕ
  | .inl ij=>ij.val.2.val-ij.val.1.val
  | .inr ij=>(r-2-ij.val.1.val)+(r-1-ij.val.2.val)+1

def height : PositiveIndex r→ℕ
  | .inl _=>0
  | .inr j=>rootHeight r j

theorem rootHeight_pos (j : RootIndex r) : 0 < rootHeight r j := by
  cases j with
  | inl ij => have h:=ij.property; change 0 < ij.val.2.val-ij.val.1.val; omega
  | inr ij => simp only [rootHeight]; omega

theorem positive_root_grade (j : RootIndex r) :
    grade r (.inr (false,j))=(rootHeight r j:ℚ) := by
  cases j with
  | inl ij =>
    have h:=ij.property
    simp only [grade,CFSGOrthogonalDUniformRootCoordinates.entry,diagonalWeight,rootHeight]
    rw [Nat.cast_sub (by omega)]
    ring
  | inr ij =>
    have hij:=ij.property
    have hil:=ij.val.1.isLt
    have hjl:=ij.val.2.isLt
    have hi : ij.val.1.val ≤ r-2 := by omega
    have hj : ij.val.2.val ≤ r-1 := by omega
    simp only [grade,CFSGOrthogonalDUniformRootCoordinates.entry,diagonalWeight,rootHeight,
      Nat.cast_add,Nat.cast_one]
    rw [Nat.cast_sub hi,Nat.cast_sub hj,Nat.cast_sub (by omega : 2 ≤ r),
      Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
    ring

theorem negative_root_grade (j : RootIndex r) :
    grade r (.inr (true,j))= -(rootHeight r j:ℚ) := by
  rw [←positive_root_grade r j]
  cases j <;> simp only [grade,CFSGOrthogonalDUniformRootCoordinates.entry,diagonalWeight] <;> ring

theorem fullIndex_grade (j : PositiveIndex r) : grade r (fullIndex r j)=(height r j:ℚ) := by
  cases j with
  | inl i => simp [fullIndex,grade,height]
  | inr j => exact positive_root_grade r j

theorem height_zero_is_cartan (j : PositiveIndex r) (hj : height r j=0) :
    ∃ i : Fin r,j=.inl i := by
  cases j with
  | inl i => exact ⟨i,rfl⟩
  | inr j => have h:=rootHeight_pos r j; change rootHeight r j=0 at hj; omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformPositiveProfile
