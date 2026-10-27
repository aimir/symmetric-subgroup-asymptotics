import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformActionGrading

/-! Uniform positive-root height profile, with Cartan height zero.
The actual diagonal grade equals this NATURAL height; negative root
coordinates have its negative. These identities turn whole graded
matrix support into the finite source induction's height conditions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformPositiveProfile
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticUniformRootGrading
variable (r : ℕ)
abbrev PositiveIndex := Fin r ⊕ RootIndex r

def fullIndex : PositiveIndex r→BasisIndex r
  | .inl i => .inl i
  | .inr j => .inr (false,j)

def rootHeight : RootIndex r→ℕ
  | .inl ij => ij.val.2.val-ij.val.1.val
  | .inr (.inl i) => 2*(r-i.val)-1
  | .inr (.inr ij) => (r-1-ij.val.1.val)+(r-ij.val.2.val)

def height : PositiveIndex r→ℕ
  | .inl _ => 0
  | .inr j => rootHeight r j

theorem rootHeight_pos (j : RootIndex r) : 0<rootHeight r j := by
  rcases j with ij | (i | ij)
  · have h:=ij.property; simp only [rootHeight];omega
  · have h:=i.isLt; simp only [rootHeight];omega
  · have h:=ij.property; have hi:=ij.val.1.isLt;have hj:=ij.val.2.isLt
    simp only [rootHeight];omega

theorem positive_root_grade (j : RootIndex r) :
    grade r (.inr (false,j))=(rootHeight r j:ℚ) := by
  rcases j with ij | (i | ij)
  · have h:=ij.property
    simp only [rootHeight,grade,CFSGSymplecticUniformRootCoordinates.entry,
      diagonalWeight]
    rw [Nat.cast_sub (by omega)]
    ring
  · have hi:=i.isLt
    simp only [rootHeight,grade,CFSGSymplecticUniformRootCoordinates.entry,
      diagonalWeight]
    rw [Nat.cast_sub (by omega),Nat.cast_mul,Nat.cast_sub (by omega)]
    norm_num
    ring
  · have h:=ij.property;have hi:=ij.val.1.isLt;have hj:=ij.val.2.isLt
    simp only [rootHeight,grade,CFSGSymplecticUniformRootCoordinates.entry,
      diagonalWeight,Nat.cast_add]
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    norm_num
    ring

theorem negative_root_grade (j : RootIndex r) :
    grade r (.inr (true,j))= -(rootHeight r j:ℚ) := by
  rw [←positive_root_grade r j]
  rcases j with ij | (i | ij) <;>
    simp only [grade,CFSGSymplecticUniformRootCoordinates.entry,diagonalWeight] <;> ring

theorem fullIndex_grade (j : PositiveIndex r) :
    grade r (fullIndex r j)=(height r j:ℚ) := by
  cases j with
  | inl i => simp [fullIndex,height,grade,CFSGSymplecticUniformRootCoordinates.entry]
  | inr j => exact positive_root_grade r j

theorem height_zero_is_cartan (j : PositiveIndex r) (hj : height r j=0) :
    ∃ i : Fin r,j=.inl i := by
  cases j with
  | inl i => exact ⟨i,rfl⟩
  | inr k => have h:=rootHeight_pos r k;change rootHeight r k=0 at hj;omega

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformPositiveProfile
