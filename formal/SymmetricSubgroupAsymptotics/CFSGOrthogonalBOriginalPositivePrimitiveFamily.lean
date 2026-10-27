import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalSumRootImage
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRationalCartanTail
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformPositiveTables

/-! The original rational positive source family has literal primitive
natural coordinates. This proves coefficient recovery ONLY on its own
finite span, without source spanning or global realization injectivity. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositivePrimitiveFamily
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreSignedRootWeights
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOriginalRootCandidates
open CFSGOrthogonalBFullMatrixCoordinates CFSGOrthogonalBUniformPositiveTables
open CFSGOrthogonalBOriginalPositiveSourceProfile
variable (r : ℕ)
local instance : DecidableEq (PositiveIndex r) := Classical.decEq _

def source : PositiveIndex r → RationalLie (CartanMatrix.B r).transpose
  | .inl i => CFSGOrthogonalBOriginalRationalCartanTail.tail r i.val
  | .inr j => (root r false j).val

private theorem integral_root_image (j : RootIndex r) :
    integralOrthogonalRepresentation r (root r false j) = matrix ℤ r (.inr (false, j)) := by
  rcases j with ij | (i | ij)
  · exact CFSGOrthogonalBOriginalPositiveRootImages.difference_image r ij
  · exact CFSGOrthogonalBOriginalPositiveRootImages.short_image r i
  · exact CFSGOrthogonalBOriginalSumRootImage.sum_image r ij

private theorem cast_positive_root_matrix (j : RootIndex r) :
    CFSGSerreSquareZeroMatrix.integerCast (Index r) (matrix ℤ r (.inr (false, j))) =
      matrix ℚ r (.inr (false, j)) := by
  ext a b
  rcases j with ij | (i | ij) <;>
    simp [matrix, CFSGSerreSquareZeroMatrix.integerCast, Matrix.map_apply,
      CFSGOrthogonalBUniformRootMatrixArithmetic.difference,
      CFSGOrthogonalBUniformRootMatrixArithmetic.short,
      CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot, Matrix.single_apply]

theorem source_image (j : PositiveIndex r) :
    rationalOrthogonalRepresentation r (source r j) = positiveMatrix r j := by
  cases j with
  | inl i =>
    simpa only [source, positiveMatrix, fullIndex, matrix,
      CFSGOrthogonalBOriginalRationalCartanTail.diagonal, dif_pos i.isLt] using
      CFSGOrthogonalBOriginalRationalCartanTail.tail_image r i.val
  | inr j =>
    change rationalOrthogonalRepresentation r (root r false j).val = matrix ℚ r (.inr (false, j))
    have h := CFSGSerreQuadraticMatrix.integralRepresentation_cast
      (realizationData r) (root r false j)
    change CFSGSerreSquareZeroMatrix.integerCast (Index r)
      (integralOrthogonalRepresentation r (root r false j)) =
        rationalOrthogonalRepresentation r (root r false j).val at h
    rw [integral_root_image, cast_positive_root_matrix] at h
    exact h.symm

def span : Submodule ℚ (RationalLie (CartanMatrix.B r).transpose) :=
  Submodule.span ℚ (Set.range (source r))

theorem coefficients_combination (a : PositiveIndex r → ℚ) :
    positiveCoordinates r (rationalOrthogonalRepresentation r
      (Fintype.linearCombination ℚ (source r) a)) = a := by
  rw [Fintype.linearCombination_apply]
  simp only [map_sum, map_smul, source_image, positive_coordinates_matrix]
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem source_eq_combination_of_mem
    (x : RationalLie (CartanMatrix.B r).transpose) (hx : x ∈ span r) :
    x = Fintype.linearCombination ℚ (source r)
      (positiveCoordinates r (rationalOrthogonalRepresentation r x)) := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  have ha' : Fintype.linearCombination ℚ (source r) a = x := by
    simpa only [Fintype.linearCombination_apply] using ha
  rw [← ha', coefficients_combination]

theorem raising_of_mem (i : Fin r) (j : PositiveIndex r)
    (hmem : ⁅rootVector (CartanMatrix.B r).transpose false i, source r j⁆ ∈ span r) :
    ⁅rootVector (CartanMatrix.B r).transpose false i, source r j⁆ =
      Fintype.linearCombination ℚ (source r) (raising r i j) := by
  have h := source_eq_combination_of_mem r _ hmem
  have hE : rationalOrthogonalRepresentation r (rootVector (CartanMatrix.B r).transpose false i) =
      positive ℚ r i := rationalOrthogonalRepresentation_E r i
  simpa only [LieHom.map_lie, hE, source_image, raising] using h

theorem lowering_of_mem (i : Fin r) (j : PositiveIndex r)
    (hmem : ⁅oppositeVector (CartanMatrix.B r).transpose false i, source r j⁆ ∈ span r) :
    ⁅oppositeVector (CartanMatrix.B r).transpose false i, source r j⁆ =
      Fintype.linearCombination ℚ (source r) (lowering r i j) := by
  have h := source_eq_combination_of_mem r _ hmem
  have hF : rationalOrthogonalRepresentation r (oppositeVector (CartanMatrix.B r).transpose false i) =
      negative ℚ r i := rationalOrthogonalRepresentation_F r i
  simpa only [LieHom.map_lie, hF, source_image, lowering] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositivePrimitiveFamily
