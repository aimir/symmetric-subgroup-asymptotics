import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformPositiveProfile
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformActionGrading
import Mathlib.Tactic.Positivity

/-! Whole natural first-action tables on Cartan plus POSITIVE roots.
The negative sector vanishes by the actual diagonal grade. Thus the
raising/lowering arrays are literal entry extraction, with genuine
whole matrix equalities and exact source-induction height support. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformPositiveTables
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformRationalFamily CFSGOrthogonalDUniformGramCoordinates
open CFSGOrthogonalDUniformGramBasis
open CFSGOrthogonalDUniformRootGrading CFSGOrthogonalDUniformActionGrading
open CFSGOrthogonalDUniformPositiveProfile
variable (r : ℕ) (hr : 4 ≤ r)

def positiveMatrix (j : PositiveIndex r) : Mat ℚ r := matrix r (fullIndex r j)

def positiveCoordinates (hr : 4 ≤ r) : Mat ℚ r→ₗ[ℚ](PositiveIndex r→ℚ) where
  toFun M j:=coordinates r hr M (fullIndex r j)
  map_add' M N:=by
    funext j
    exact congrFun (map_add (coordinates r hr) M N) (fullIndex r j)
  map_smul' a M:=by
    funext j
    exact congrFun (map_smul (coordinates r hr) a M) (fullIndex r j)

def raising (i : Fin r) (j : PositiveIndex r) : PositiveIndex r→ℚ :=
  positiveCoordinates r hr ⁅positive ℚ r i,positiveMatrix r j⁆
def lowering (i : Fin r) (j : PositiveIndex r) : PositiveIndex r→ℚ :=
  positiveCoordinates r hr ⁅negative ℚ r i,positiveMatrix r j⁆

theorem fullIndex_injective : Function.Injective (fullIndex r) := by
  intro j k h
  cases j <;> cases k <;> simp_all [fullIndex]

theorem positive_coordinates_matrix (j : PositiveIndex r) :
    positiveCoordinates r hr (positiveMatrix r j)=Pi.single j 1 := by
  funext k
  change coordinates r hr (matrix r (fullIndex r j)) (fullIndex r k)=_
  rw [coordinates_matrix]
  simp [Pi.single_apply,(fullIndex_injective r).eq_iff]

private theorem negative_coordinate_zero (M : Mat ℚ r) (g : ℚ) (hg : 0≤g)
    (hM : ⁅gradingMatrix r,M⁆=g • M) (j : RootIndex r) :
    coordinates r hr M (.inr (true,j))=0 := by
  by_contra hc
  have h:=congrArg (fun X : Mat ℚ r=>coordinates r hr X (.inr (true,j))) hM
  simp only [bracket_coordinate,map_smul,Pi.smul_apply,smul_eq_mul] at h
  have he:=mul_right_cancel₀ hc h
  rw [negative_root_grade] at he
  have hp : (0:ℚ)<rootHeight r j:=by exact_mod_cast rootHeight_pos r j
  linarith

theorem positive_reconstruction (M : Mat ℚ r) (hB : Orthogonal r M)
    (g : ℚ) (hg : 0≤g) (hM : ⁅gradingMatrix r,M⁆=g • M) :
    Fintype.linearCombination ℚ (positiveMatrix r) (positiveCoordinates r hr M)=M := by
  have h:=reconstruction r hr M hB
  have hz:=negative_coordinate_zero r hr M g hg hM
  simpa only [Fintype.linearCombination_apply,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fintype.sum_bool,hz,zero_smul,Finset.sum_const_zero,
    zero_add,positiveMatrix,positiveCoordinates,fullIndex] using h

include hr in
private theorem bracket_weight (U : Mat ℚ r) (u : ℚ)
    (hU : ⁅gradingMatrix r,U⁆=u • U) (j : PositiveIndex r) :
    ⁅gradingMatrix r,⁅U,positiveMatrix r j⁆⁆=
      (u+(height r j:ℚ)) • ⁅U,positiveMatrix r j⁆ := by
  rw [leibniz_lie,hU]
  change ⁅u • U,positiveMatrix r j⁆+
    ⁅U,⁅gradingMatrix r,matrix r (fullIndex r j)⁆⁆=_
  rw [matrix_weight r hr,fullIndex_grade,smul_lie,lie_smul,add_smul]
  rfl

theorem raising_table (i : Fin r) (j : PositiveIndex r) :
    ⁅positive ℚ r i,positiveMatrix r j⁆=
      Fintype.linearCombination ℚ (positiveMatrix r) (raising r hr i j) := by
  apply (positive_reconstruction r hr _
    ((skewAdjointMatricesLieSubalgebra (gram ℚ r)).lie_mem
      (positive_mem_orthogonal ℚ r i) (matrix_mem r (fullIndex r j)))
    ((1:ℚ)+(height r j:ℚ)) (by positivity) _).symm
  exact bracket_weight r hr _ 1 (by simpa only [one_smul] using positive_weight r hr i) j

theorem lowering_table (i : Fin r) (j : PositiveIndex r) (hj : 0<height r j) :
    ⁅negative ℚ r i,positiveMatrix r j⁆=
      Fintype.linearCombination ℚ (positiveMatrix r) (lowering r hr i j) := by
  have hg : (0:ℚ)≤ -1+(height r j:ℚ) := by
    have h : (1:ℚ)≤height r j:=by exact_mod_cast hj
    linarith
  apply (positive_reconstruction r hr _
    ((skewAdjointMatricesLieSubalgebra (gram ℚ r)).lie_mem
      (negative_mem_orthogonal ℚ r i) (matrix_mem r (fullIndex r j)))
    ((-1:ℚ)+(height r j:ℚ)) hg _).symm
  exact bracket_weight r hr _ (-1) (negative_weight r hr i) j

theorem raising_height (i : Fin r) (j k : PositiveIndex r)
    (hc : raising r hr i j k≠0) : height r k=height r j+1 := by
  have h:=raising_support r hr i (fullIndex r j) (fullIndex r k) hc
  rw [fullIndex_grade,fullIndex_grade] at h
  have he : (height r k:ℚ)=((height r j+1:ℕ):ℚ) := by
    simp only [Nat.cast_add,Nat.cast_one]
    linarith
  exact_mod_cast he

theorem lowering_height (i : Fin r) (j k : PositiveIndex r)
    (hc : lowering r hr i j k≠0) : height r k+1=height r j := by
  have h:=lowering_support r hr i (fullIndex r j) (fullIndex r k) hc
  rw [fullIndex_grade,fullIndex_grade] at h
  have he : ((height r k+1:ℕ):ℚ)=(height r j:ℚ) := by
    simp only [Nat.cast_add,Nat.cast_one]
    linarith
  exact_mod_cast he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformPositiveTables
