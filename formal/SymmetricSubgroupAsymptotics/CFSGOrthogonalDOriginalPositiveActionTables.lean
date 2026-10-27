import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveInductionParents
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveMixedCoefficients
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveComparison
import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootFamilyInduction

/-! ALL original positive-source raising/lowering actions, derived by
height induction from the actual parent paths and original Serre
relations. No source-action table or realization-faithfulness premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveActionTables
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights
open CFSGOrthogonalDUniformPositiveProfile CFSGOrthogonalDUniformPositiveTables
open CFSGOrthogonalDUniformCorootWeights CFSGOrthogonalDOriginalPositiveSourceWeights
variable (r : ℕ) (hr : 4 ≤ r)

theorem source_tables :
    (∀ i j,⁅rootVector (CartanMatrix.D r) false i,source r hr j⁆=
      Fintype.linearCombination ℚ (source r hr) (raising r hr i j)) ∧
    (∀ a j,0 < height r j→⁅oppositeVector (CartanMatrix.D r) false a,source r hr j⁆=
      Fintype.linearCombination ℚ (source r hr) (lowering r hr a j)) := by
  apply CFSGSerreFiniteRootFamilyInduction.source_tables
    (CartanMatrix.D r) (source r hr) false (height r)
    (CFSGOrthogonalDUniformCorootWeights.weight r) (raising r hr) (lowering r hr)
  · intro a
    exact CartanMatrix.D_diag r a
  · exact CFSGOrthogonalDOriginalPositiveWeightIdentification.source_weight r hr
  · exact CFSGOrthogonalDOriginalPositiveBaseActions.raising_base r hr
  · exact CFSGOrthogonalDOriginalPositiveBaseActions.lowering_base r hr
  · intro a j hj l hl
    exact lowering_height r hr a j l hl
  · intro i j hj l hl
    exact raising_height r hr i j l hl
  · intro i a j hj l hl
    exact raising_weight r hr i a j l hl
  · intro i j hj
    exact CFSGOrthogonalDPositiveComparison.positive_comparison r hr i j
  · exact CFSGOrthogonalDOriginalPositiveInductionParents.induction_parent r hr
  · exact CFSGOrthogonalDPositiveMixedCoefficients.mixed_coefficients r hr

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveActionTables
