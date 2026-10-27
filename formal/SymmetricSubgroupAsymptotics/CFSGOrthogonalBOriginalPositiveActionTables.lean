import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveInductionParents
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveMixedCoefficients
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveComparison
import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootFamilyInduction

/-! All original B positive-source raising/lowering actions, derived
by genuine source height induction. No realization-injectivity or source
basis premise appears in this theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveActionTables
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights
open CFSGOrthogonalBOriginalPositiveSourceProfile CFSGOrthogonalBUniformPositiveTables
variable (r : ℕ)

theorem source_tables :
    (∀ i j, ⁅rootVector (CartanMatrix.B r).transpose false i,
      CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j⁆ =
      Fintype.linearCombination ℚ (CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r)
        (raising r i j)) ∧
    (∀ a j, 0 < height r j → ⁅oppositeVector (CartanMatrix.B r).transpose false a,
      CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j⁆ =
      Fintype.linearCombination ℚ (CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r)
        (lowering r a j)) := by
  apply CFSGSerreFiniteRootFamilyInduction.source_tables
    (CartanMatrix.B r).transpose (CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r)
    false (height r) (CFSGOrthogonalBUniformCorootWeights.weight r) (raising r) (lowering r)
  · intro a
    simpa only [Matrix.transpose_apply] using CartanMatrix.B_diag r a
  · exact CFSGOrthogonalBOriginalPositiveWeightIdentification.source_weight r
  · exact CFSGOrthogonalBOriginalPositiveBaseActions.raising_base r
  · exact CFSGOrthogonalBOriginalPositiveBaseActions.lowering_base r
  · intro a j hj l hl
    exact lowering_height r a j l hl
  · intro i j hj l hl
    exact raising_height r i j l hl
  · intro i a j hj l hl
    exact CFSGOrthogonalBUniformCorootWeights.raising_weight r i a j l hl
  · intro i j hj
    exact CFSGOrthogonalBPositiveComparison.positive_comparison r i j
  · exact CFSGOrthogonalBOriginalPositiveInductionParents.induction_parent r
  · exact CFSGOrthogonalBPositiveMixedCoefficients.mixed_coefficients r

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveActionTables
