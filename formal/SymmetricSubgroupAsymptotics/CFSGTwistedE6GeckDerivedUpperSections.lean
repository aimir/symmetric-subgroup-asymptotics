import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedRootSections
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedSourceUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootCoordinateLifts

/-! The actual upper preimage of the ORIGINAL Derived action range is
fixed, and contains every literal fixed singleton or paired orbit section.
These local memberships are proved from the displayed original sections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedUpperSections
open CFSGTwistedE6GeckDerivedRootSections CFSGTwistedE6GeckSingletonDerivedSeeds
open CFSGTwistedE6GeckFixedSourceUpper CFSGTwistedE6GeckPositiveCoordinateLifts
open CFSGTwistedE6GeckRootCoordinateLifts CFSGTwistedE6GeckPositiveActionInjective
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckSectionParameterTwist CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6GeckSectionDiagramLabels CFSGTwistedE6GeckOriginalRootSections
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6WeylChamber CFSGTwistedE6FixedA2
open CFSGSerreOrdinaryTwists

def derivedUpper (q : CFSG.PrimePower) : Subgroup (Positive (q.Extension 2)) :=
  (derivedImageAction q).range.comap (positiveAction (q.Extension 2))

theorem derivedUpper_le_fixedSourceUpper (q : CFSG.PrimePower) :
    derivedUpper q≤fixedSourceUpper q := by
  rintro u ⟨d,hd⟩
  apply (mem_fixedSourceUpper_iff q u).mpr
  exact ⟨d.val,hd⟩

theorem derivedUpper_fixed (q : CFSG.PrimePower) (u : Positive (q.Extension 2))
    (hu : u∈derivedUpper q) :
    positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) u=u :=
  fixedSourceUpper_fixed q u (derivedUpper_le_fixedSourceUpper q hu)

theorem singleton_mem_derivedUpper (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val=k.val) (x : RootLine (q.Extension 2) k.val)
    (hx : unitTwist (q.Extension 2) (definingFieldAutomorphism q 2) x.val=x.val) :
    rootLinePositive (q.Extension 2) k x∈derivedUpper q := by
  obtain ⟨t,ht,hm⟩ := rootLine_chart q k x
  have hfixed : unitTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (sectionParameter (q.Extension 2) k t).val=(sectionParameter (q.Extension 2) k t).val := by
    rw [ht]
    exact hx
  have hscalar := (singleton_parameter_fixed_iff q k hk t).mp hfixed
  have hnode := (section_seed_fixed_iff k).mpr hk
  have hmem := singletonSection_action_mem_derived q k hnode t hscalar
  have he : imageAction q (singletonSection q k hnode t hscalar)=
      positiveAction (q.Extension 2) (rootLinePositive (q.Extension 2) k x) := by
    change imageAction q (singletonSection q k hnode t hscalar)=matrixAction (q.Extension 2)
      (positiveInclusion (q.Extension 2) (rootLinePositive (q.Extension 2) k x))
    rw [rootLinePositive_matrix,hm]
    exact singletonSection_action q k hnode t hscalar
  change positiveAction (q.Extension 2) (rootLinePositive (q.Extension 2) k x)∈
    (derivedImageAction q).range
  rw [←he]
  exact hmem

theorem pair_mem_derivedUpper (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val≠k.val) (x : RootLine (q.Extension 2) k.val) :
    rootLinePositive (q.Extension 2) k x*
      positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
        (rootLinePositive (q.Extension 2) k x)∈derivedUpper q := by
  obtain ⟨t,_,hm⟩ := rootLine_chart q k x
  have hnode : CFSG.Models.e6Twist (sectionNode k)≠sectionNode k :=
    fun h=>hk ((section_seed_fixed_iff k).mp h)
  have hmem := pairedSection_action_mem_derived q k hnode t
  have he : imageAction q (pairedSection q k hnode t)=matrixAction (q.Extension 2)
      (rootLineToMatrix (q.Extension 2) k.val x*
        matrixGroupTwist (q.Extension 2) (definingFieldAutomorphism q 2)
          (rootLineToMatrix (q.Extension 2) k.val x)) := by
    rw [pairedSection_action,hm,firstMatrixRoot_twist]
    apply congrArg (matrixAction (q.Extension 2))
    dsimp only [firstMatrixRoot,secondMatrixRoot]
    rw [definingFieldAutomorphism_apply]
    group
  have hp : positiveAction (q.Extension 2)
      (rootLinePositive (q.Extension 2) k x*
        positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
          (rootLinePositive (q.Extension 2) k x))=matrixAction (q.Extension 2)
      (rootLineToMatrix (q.Extension 2) k.val x*
        matrixGroupTwist (q.Extension 2) (definingFieldAutomorphism q 2)
          (rootLineToMatrix (q.Extension 2) k.val x)) := by
    change matrixAction (q.Extension 2) (positiveInclusion (q.Extension 2)
      (rootLinePositive (q.Extension 2) k x*
        positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
          (rootLinePositive (q.Extension 2) k x)))=_
    rw [map_mul,positiveInclusion_twist,rootLinePositive_matrix]
  change positiveAction (q.Extension 2) _∈(derivedImageAction q).range
  rw [hp,←he]
  exact hmem

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedUpperSections
