import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionParameterTwist

/-! Actual singleton and paired intrinsic root-line coordinates admit
literal ORIGINAL fixed-subgroup witnesses with the same matrix action.
For singleton coordinates the needed subfield parameter is recovered
from actual fixedness and chart injectivity, not supplied as a premise.
No source faithfulness or derived membership is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootCoordinateLifts
open CFSGTwistedE6GeckSectionParameterTwist CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6GeckSectionDiagramLabels CFSGTwistedE6GeckOriginalRootSections
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckSourceActionCovariance CFSGTwistedE6GeckDiagramCovariance
open CFSGNormTwoCoordinateRootSubgroup CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGTwistedE6FixedA2 CFSGTwistedE6WeylChamber CFSGSerreOrdinaryTwists

def rootLineToMatrix (K : Type) [Field K] (k : Roots CartanMatrix.E₆) : RootLine K k→*MatrixGroup K :=
  Subgroup.inclusion (rootSubgroup_le_elementary CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k)

theorem rootLineToMatrix_val (K : Type) [Field K] (k : Roots CartanMatrix.E₆) (x : RootLine K k) :
    (rootLineToMatrix K k x).val=x.val := rfl

theorem rootLine_chart (q : CFSG.PrimePower) (k : PositiveRoot) (x : RootLine (q.Extension 2) k.val) :
    ∃t : q.Extension 2,sectionParameter (q.Extension 2) k t=x ∧
      rootLineToMatrix (q.Extension 2) k.val x=firstMatrixRoot q k t := by
  obtain ⟨a,ha⟩ := (sectionParameterMulEquiv (q.Extension 2) k).surjective x
  refine ⟨a.toAdd,ha,?_⟩
  apply Subtype.ext
  change x.val=(firstMatrixRoot q k a.toAdd).val
  rw [firstMatrixRoot_val]
  exact (congrArg Subtype.val ha).symm

theorem exists_original_singleton_coordinate (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val=k.val) (x : RootLine (q.Extension 2) k.val)
    (hx : unitTwist (q.Extension 2) (definingFieldAutomorphism q 2) x.val=x.val) :
    ∃s : Fixed q,imageAction q s=matrixAction (q.Extension 2) (rootLineToMatrix (q.Extension 2) k.val x) := by
  obtain ⟨t,ht,hm⟩ := rootLine_chart q k x
  have hfixed : unitTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (sectionParameter (q.Extension 2) k t).val=(sectionParameter (q.Extension 2) k t).val := by
    rw [ht]
    exact hx
  have hscalar := (singleton_parameter_fixed_iff q k hk t).mp hfixed
  have hnode := (section_seed_fixed_iff k).mpr hk
  refine ⟨singletonSection q k hnode t hscalar,?_⟩
  rw [hm]
  exact singletonSection_action q k hnode t hscalar

theorem exists_original_paired_coordinate (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val≠k.val) (x : RootLine (q.Extension 2) k.val) :
    ∃s : Fixed q,imageAction q s=matrixAction (q.Extension 2)
      (rootLineToMatrix (q.Extension 2) k.val x*
        matrixGroupTwist (q.Extension 2) (definingFieldAutomorphism q 2)
          (rootLineToMatrix (q.Extension 2) k.val x)) := by
  obtain ⟨t,_,hm⟩ := rootLine_chart q k x
  have hnode : CFSG.Models.e6Twist (sectionNode k)≠sectionNode k :=
    fun h=>hk ((section_seed_fixed_iff k).mp h)
  refine ⟨pairedSection q k hnode t,?_⟩
  rw [pairedSection_action,hm,firstMatrixRoot_twist]
  apply congrArg (matrixAction (q.Extension 2))
  dsimp only [firstMatrixRoot,secondMatrixRoot]
  rw [definingFieldAutomorphism_apply]
  group

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootCoordinateLifts
