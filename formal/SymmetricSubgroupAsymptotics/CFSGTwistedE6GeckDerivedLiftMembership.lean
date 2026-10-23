import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckActionRangeTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6DerivedRootImages
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLiftMembership

/-! An action of the ORIGINAL derived pinned fixed E6 group admits an
actual twist-fixed matrix lift inside the commutator of the exact action
preimage. The proof uses the proved central kernel, not source faithfulness
or pointwise fixedness of the kernel. Whole fixed-root generation remains
separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedLiftMembership
open CFSGTwistedE6GeckActionRangeTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
open CFSGCentralTwistedCommutatorLift

def fixedRangeAction (q : CFSG.PrimePower) : Fixed q→*
    CFSGCentralTwistedCommutatorLift.fixedSubgroup
      (actionRangeTwist (q.Extension 2) (definingFieldAutomorphism q 2)) :=
  (originalFixedRangeAction q).codRestrict _ (originalFixedRangeAction_fixed q)

theorem fixedRangeAction_mem_commutator (q : CFSG.PrimePower) (g : Derived q) :
    fixedRangeAction q g.val∈commutator
      (CFSGCentralTwistedCommutatorLift.fixedSubgroup
        (actionRangeTwist (q.Extension 2) (definingFieldAutomorphism q 2))) := by
  have hmap : (commutator (Fixed q)).map (fixedRangeAction q)≤commutator
      (CFSGCentralTwistedCommutatorLift.fixedSubgroup
        (actionRangeTwist (q.Extension 2) (definingFieldAutomorphism q 2))) := by
    simp only [commutator_def,Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hmap ⟨g.val,g.property,rfl⟩

def fixedActionPreimage (q : CFSG.PrimePower) : Subgroup (MatrixGroup (q.Extension 2)) :=
  fixedPreimage (matrixRangeProjection (q.Extension 2))
    (actionRangeTwist (q.Extension 2) (definingFieldAutomorphism q 2))

theorem exists_original_derived_lift_in_commutator (q : CFSG.PrimePower) (g : Derived q) :
    ∃v : fixedActionPreimage q,v∈commutator (fixedActionPreimage q) ∧
      matrixGroupTwist (q.Extension 2) (definingFieldAutomorphism q 2) v.val=v.val ∧
      matrixAction (q.Extension 2) v.val=derivedImageAction q g := by
  obtain ⟨v,hv,hfixed,he⟩ := exists_fixed_lift_in_preimage_commutator
    (matrixRangeProjection (q.Extension 2)) (matrixRangeProjection_surjective (q.Extension 2))
    (matrixRangeProjection_kernel_le_center (q.Extension 2))
    (matrixGroupTwist (q.Extension 2) (definingFieldAutomorphism q 2))
    (actionRangeTwist (q.Extension 2) (definingFieldAutomorphism q 2))
    (matrixRangeProjection_twist (q.Extension 2) (definingFieldAutomorphism q 2))
    (fixedRangeAction q g.val) (fixedRangeAction_mem_commutator q g)
  exact ⟨v,hv,hfixed,congrArg Subtype.val he⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedLiftMembership
