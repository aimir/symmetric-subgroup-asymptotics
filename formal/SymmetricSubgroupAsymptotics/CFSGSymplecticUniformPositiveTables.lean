import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformPositiveProfile
import Mathlib.Tactic.Positivity

/-! Whole natural first-action tables on Cartan plus POSITIVE roots.
The negative sector vanishes by the actual diagonal grade. Thus the
raising/lowering arrays are literal entry extraction, with genuine
whole matrix equalities and exact source-induction height support. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformPositiveTables
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticUniformRootCoordinates CFSGSymplecticUniformBlockCoordinates
open CFSGSymplecticUniformBlockLie CFSGSymplecticUniformBlockBasis
open CFSGSymplecticUniformRootGrading CFSGSymplecticUniformActionGrading
open CFSGSymplecticUniformPositiveProfile
variable (r : ℕ)

def positiveMatrix (j : PositiveIndex r) : Mat ℚ r := matrix ℚ r (fullIndex r j)

def positiveCoordinates : Mat ℚ r→ₗ[ℚ](PositiveIndex r→ℚ) where
  toFun M j:=coordinates ℚ r M (fullIndex r j)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def raising (i : Fin r) (j : PositiveIndex r) : PositiveIndex r→ℚ :=
  positiveCoordinates r ⁅positive ℚ r i,positiveMatrix r j⁆
def lowering (i : Fin r) (j : PositiveIndex r) : PositiveIndex r→ℚ :=
  positiveCoordinates r ⁅negative ℚ r i,positiveMatrix r j⁆

theorem fullIndex_injective : Function.Injective (fullIndex r) := by
  intro j k h
  cases j <;> cases k <;> simp_all [fullIndex]

theorem positive_coordinates_matrix (j : PositiveIndex r) :
    positiveCoordinates r (positiveMatrix r j)=Pi.single j 1 := by
  funext k
  change coordinates ℚ r (matrix ℚ r (fullIndex r j)) (fullIndex r k)=_
  rw [coordinates_matrix]
  simp [Pi.single_apply,(fullIndex_injective r).eq_iff]

private theorem negative_coordinate_zero (M : Mat ℚ r) (g : ℚ) (hg : 0≤g)
    (hM : ⁅gradingMatrix r,M⁆=g • M) (j : RootIndex r) :
    coordinates ℚ r M (.inr (true,j))=0 := by
  by_contra hc
  have h:=congrArg (fun X : Mat ℚ r=>coordinates ℚ r X (.inr (true,j))) hM
  simp only [bracket_coordinate,map_smul,Pi.smul_apply,smul_eq_mul] at h
  have he:=mul_right_cancel₀ hc h
  rw [negative_root_grade] at he
  have hp : (0:ℚ)<rootHeight r j:=by exact_mod_cast rootHeight_pos r j
  linarith

theorem positive_reconstruction (M : Mat ℚ r) (hB : Block ℚ r M)
    (g : ℚ) (hg : 0≤g) (hM : ⁅gradingMatrix r,M⁆=g • M) :
    Fintype.linearCombination ℚ (positiveMatrix r) (positiveCoordinates r M)=M := by
  have h:=reconstruction ℚ r M hB
  have hz:=negative_coordinate_zero r M g hg hM
  simpa only [Fintype.linearCombination_apply,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fintype.sum_bool,hz,zero_smul,Finset.sum_const_zero,
    zero_add,positiveMatrix,positiveCoordinates,fullIndex] using h

private theorem simple_mem (i : Fin r) : Block ℚ r (positive ℚ r i) := by
  by_cases hi : i.val+1<r
  · let next : Fin r:=⟨i.val+1,hi⟩
    let ij : Pair r:=⟨(i,next),by dsimp [next];omega⟩
    have h:=matrix_mem ℚ r (.inr (false,.inl ij))
    simpa only [positive,dif_pos hi,matrix,ij,next] using h
  · have h:=matrix_mem ℚ r (.inr (false,.inr (.inl i)))
    simpa only [positive,dif_neg hi,matrix] using h

private theorem transpose_mem (M : Mat ℚ r) (hM : Block ℚ r M) :
    Block ℚ r M.transpose := by
  exact ⟨fun i j=>hM.1 j i,fun i j=>hM.2.2 j i,fun i j=>hM.2.1 j i⟩

private theorem bracket_weight (U : Mat ℚ r) (u : ℚ)
    (hU : ⁅gradingMatrix r,U⁆=u • U) (j : PositiveIndex r) :
    ⁅gradingMatrix r,⁅U,positiveMatrix r j⁆⁆=
      (u+(height r j:ℚ)) • ⁅U,positiveMatrix r j⁆ := by
  rw [leibniz_lie,hU]
  change ⁅u • U,positiveMatrix r j⁆+
    ⁅U,⁅gradingMatrix r,matrix ℚ r (fullIndex r j)⁆⁆=_
  rw [matrix_weight,fullIndex_grade,smul_lie,lie_smul,add_smul]
  rfl

theorem raising_table (i : Fin r) (j : PositiveIndex r) :
    ⁅positive ℚ r i,positiveMatrix r j⁆=
      Fintype.linearCombination ℚ (positiveMatrix r) (raising r i j) := by
  apply (positive_reconstruction r _
    (lie_mem ℚ r _ _ (simple_mem r i) (matrix_mem ℚ r (fullIndex r j)))
    (1+height r j) (by positivity) _).symm
  exact bracket_weight r _ 1 (by simpa only [one_smul] using positive_weight r i) j

theorem lowering_table (i : Fin r) (j : PositiveIndex r) (hj : 0<height r j) :
    ⁅negative ℚ r i,positiveMatrix r j⁆=
      Fintype.linearCombination ℚ (positiveMatrix r) (lowering r i j) := by
  have hg : (0:ℚ)≤ -1+(height r j:ℚ) := by
    have h : (1:ℚ)≤height r j:=by exact_mod_cast hj
    linarith
  apply (positive_reconstruction r _
    (lie_mem ℚ r _ _ (transpose_mem r _ (simple_mem r i))
      (matrix_mem ℚ r (fullIndex r j)))
    (-1+height r j) hg _).symm
  exact bracket_weight r _ (-1) (negative_weight r i) j

theorem raising_height (i : Fin r) (j k : PositiveIndex r)
    (hc : raising r i j k≠0) : height r k=height r j+1 := by
  have h:=raising_support r i (fullIndex r j) (fullIndex r k) hc
  rw [fullIndex_grade,fullIndex_grade] at h
  have he : (height r k:ℚ)=((height r j+1:ℕ):ℚ) := by
    simp only [Nat.cast_add,Nat.cast_one]
    linarith
  exact_mod_cast he

theorem lowering_height (i : Fin r) (j k : PositiveIndex r)
    (hc : lowering r i j k≠0) : height r k+1=height r j := by
  have h:=lowering_support r i (fullIndex r j) (fullIndex r k) hc
  rw [fullIndex_grade,fullIndex_grade] at h
  have he : ((height r k+1:ℕ):ℚ)=(height r j:ℚ) := by
    simp only [Nat.cast_add,Nat.cast_one]
    linarith
  exact_mod_cast he

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformPositiveTables
