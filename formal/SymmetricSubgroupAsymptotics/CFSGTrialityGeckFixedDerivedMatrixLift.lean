import SymmetricSubgroupAsymptotics.CFSGTrialityGeckActionRangeTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixActionCentralKernel
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveDerivedImage
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift

/-! Actions of the DERIVED original fixed subgroup admit actual fixed
matrix lifts.  This uses the genuine central kernel and covariance, not
surjectivity on arbitrary fixed points or pointwise fixedness of the kernel.
It does not identify the entire fixed matrix group with its positive and
negative root generators. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedDerivedMatrixLift
open CFSGTrialityGeckActionRangeTwist CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckMatrixActionCentralKernel CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckOriginalFixedSections CFSGTrialityGeckLongDerivedImage
open CFSGTrialityGeckFixedPositiveDerivedImage CFSGTrialityTripleFixedRoots
open CFSGSerreOrdinaryTwists

def fixedRangeAction (q : CFSG.PrimePower) : Fixed q →*
    CFSGCentralTwistedCommutatorLift.fixedSubgroup
      (actionRangeTwist (q.Extension 3) (definingFieldAutomorphism q 3)) :=
  (originalFixedRangeAction q).codRestrict _ (originalFixedRangeAction_fixed q)

theorem fixedRangeAction_mem_commutator (q : CFSG.PrimePower)
    (g : commutator (Fixed q)) :
    fixedRangeAction q g.val ∈ commutator
      (CFSGCentralTwistedCommutatorLift.fixedSubgroup
        (actionRangeTwist (q.Extension 3) (definingFieldAutomorphism q 3))) := by
  have hmap : (commutator (Fixed q)).map (fixedRangeAction q) ≤ commutator
      (CFSGCentralTwistedCommutatorLift.fixedSubgroup
        (actionRangeTwist (q.Extension 3) (definingFieldAutomorphism q 3))) := by
    simp only [commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hmap ⟨g.val, g.property, rfl⟩

theorem exists_fixed_matrix_lift (q : CFSG.PrimePower)
    (g : commutator (Fixed q)) :
    ∃ v : MatrixGroup (q.Extension 3),
      matrixGroupTwist (q.Extension 3) (definingFieldAutomorphism q 3) v = v ∧
      matrixAction (q.Extension 3) v = derivedImageAction q g := by
  obtain ⟨v, hv, he⟩ :=
    CFSGCentralTwistedCommutatorLift.exists_fixed_lift_of_mem_commutator_fixed
      (matrixRangeProjection (q.Extension 3))
      (matrixRangeProjection_surjective (q.Extension 3))
      (matrixRangeProjection_kernel_le_center (q.Extension 3))
      (matrixGroupTwist (q.Extension 3) (definingFieldAutomorphism q 3))
      (actionRangeTwist (q.Extension 3) (definingFieldAutomorphism q 3))
      (matrixRangeProjection_twist (q.Extension 3) (definingFieldAutomorphism q 3))
      (fixedRangeAction q g.val) (fixedRangeAction_mem_commutator q g)
  refine ⟨v, hv, ?_⟩
  exact congrArg Subtype.val he

abbrev FixedMatrixGroup (q : CFSG.PrimePower) :=
  CFSGCentralTwistedCommutatorLift.fixedSubgroup
    (matrixGroupTwist (q.Extension 3) (definingFieldAutomorphism q 3))

def fixedMatrixAction (q : CFSG.PrimePower) : FixedMatrixGroup q →*
    (Image (q.Extension 3) ≃ₗ[q.Extension 3] Image (q.Extension 3)) :=
  (matrixAction (q.Extension 3)).comp (FixedMatrixGroup q).subtype

theorem derived_action_range_le_fixed_matrix_action (q : CFSG.PrimePower) :
    (derivedImageAction q).range ≤ (fixedMatrixAction q).range := by
  rintro y ⟨g, rfl⟩
  obtain ⟨v, hv, he⟩ := exists_fixed_matrix_lift q g
  exact ⟨⟨v, hv⟩, he⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedDerivedMatrixLift
