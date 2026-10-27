import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveInductionParents
import SymmetricSubgroupAsymptotics.CFSGSymplecticPositiveMixedCoefficients
import SymmetricSubgroupAsymptotics.CFSGSymplecticPositiveComparison
import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootFamilyInduction

/-! ALL original positive-source raising/lowering actions, derived by
height induction from the actual parent paths and original Serre
relations. No source-action table or realization-faithfulness premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveActionTables
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights
open CFSGSymplecticUniformPositiveProfile CFSGSymplecticUniformPositiveTables
open CFSGSymplecticUniformCorootWeights CFSGSymplecticOriginalPositiveSourceWeights
variable (r : ℕ)

theorem source_tables :
    (∀ i j,⁅rootVector (CartanMatrix.C r).transpose false i,source r j⁆=
      Fintype.linearCombination ℚ (source r) (raising r i j)) ∧
    (∀ a j,0 < height r j→⁅oppositeVector (CartanMatrix.C r).transpose false a,source r j⁆=
      Fintype.linearCombination ℚ (source r) (lowering r a j)) := by
  apply CFSGSerreFiniteRootFamilyInduction.source_tables
    (CartanMatrix.C r).transpose (source r) false (height r)
    (CFSGSymplecticUniformCorootWeights.weight r) (raising r) (lowering r)
  · intro a
    simpa only [Matrix.transpose_apply] using CartanMatrix.C_diag r a
  · exact CFSGSymplecticOriginalPositiveWeightIdentification.source_weight r
  · exact CFSGSymplecticOriginalPositiveBaseActions.raising_base r
  · exact CFSGSymplecticOriginalPositiveBaseActions.lowering_base r
  · intro a j hj l hl
    exact lowering_height r a j l hl
  · intro i j hj l hl
    exact raising_height r i j l hl
  · intro i a j hj l hl
    exact raising_weight r i a j l hl
  · intro i j hj
    exact CFSGSymplecticPositiveComparison.positive_comparison r i j
  · exact CFSGSymplecticOriginalPositiveInductionParents.induction_parent r
  · exact CFSGSymplecticPositiveMixedCoefficients.mixed_coefficients r

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveActionTables
