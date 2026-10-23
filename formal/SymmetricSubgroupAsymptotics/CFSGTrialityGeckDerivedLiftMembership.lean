import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedDerivedMatrixLift
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLiftMembership

/-! Original derived triality actions have fixed matrix lifts inside the
commutator of the exact action preimage. The retained membership permits
the root-generation argument on that preimage to reach the SAME original
derived action; fixed-point exactness is not asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedLiftMembership
open CFSGCentralTwistedCommutatorLift CFSGTrialityGeckActionRangeTwist
open CFSGTrialityGeckMatrixGroupTwist CFSGTrialityGeckMatrixActionCentralKernel
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckFixedDerivedMatrixLift
open CFSGTrialityTripleFixedRoots CFSGTrialityGeckLongDerivedImage
open CFSGSerreOrdinaryTwists

def fixedActionPreimage (q : CFSG.PrimePower) : Subgroup (MatrixGroup (q.Extension 3)) :=
  fixedPreimage (matrixRangeProjection (q.Extension 3))
    (actionRangeTwist (q.Extension 3) (definingFieldAutomorphism q 3))

theorem exists_original_derived_lift_in_commutator (q : CFSG.PrimePower)
    (g : commutator (Fixed q)) :
    ∃ v : fixedActionPreimage q, v ∈ commutator (fixedActionPreimage q) ∧
      matrixGroupTwist (q.Extension 3) (definingFieldAutomorphism q 3) v.val = v.val ∧
      matrixAction (q.Extension 3) v.val = derivedImageAction q g := by
  obtain ⟨v, hv, hfixed, he⟩ := exists_fixed_lift_in_preimage_commutator
    (matrixRangeProjection (q.Extension 3)) (matrixRangeProjection_surjective (q.Extension 3))
    (matrixRangeProjection_kernel_le_center (q.Extension 3))
    (matrixGroupTwist (q.Extension 3) (definingFieldAutomorphism q 3))
    (actionRangeTwist (q.Extension 3) (definingFieldAutomorphism q 3))
    (matrixRangeProjection_twist (q.Extension 3) (definingFieldAutomorphism q 3))
    (fixedRangeAction q g.val) (fixedRangeAction_mem_commutator q g)
  exact ⟨v, hv, hfixed, congrArg Subtype.val he⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedLiftMembership
