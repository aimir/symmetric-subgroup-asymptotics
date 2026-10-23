import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveActionInjective
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootCoordinateLifts
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIntrinsicHeightLayer

/-! Actual singleton and paired root-line sections lift to fixed elements
of the literal upper group, with ORIGINAL fixed-source witnesses. Paired
matrix fixedness follows from the proved upper-action injectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveCoordinateLifts
open CFSGTwistedE6GeckPositiveActionInjective CFSGTwistedE6GeckRootCoordinateLifts
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckOriginalRootSections
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6WeylChamber
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoCoordinateIntrinsicHeightLayer CFSGTwistedE6FixedA2
open CFSGSerreOrdinaryTwists

def rootLinePositive (K : Type) [Field K] (k : PositiveRoot) :
    RootLine K k.val →* Positive K :=
  rootLineInclusion CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val k.property

theorem rootLinePositive_val (K : Type) [Field K] (k : PositiveRoot)
    (x : RootLine K k.val) : (rootLinePositive K k x).val=x.val := rfl

theorem rootLinePositive_matrix (K : Type) [Field K] (k : PositiveRoot)
    (x : RootLine K k.val) :
    positiveInclusion K (rootLinePositive K k x)=rootLineToMatrix K k.val x := rfl

theorem singleton_positive_witness (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val=k.val) (x : RootLine (q.Extension 2) k.val)
    (hx : unitTwist (q.Extension 2) (definingFieldAutomorphism q 2) x.val=x.val) :
    ∃s : Fixed q,imageAction q s=positiveAction (q.Extension 2)
      (rootLinePositive (q.Extension 2) k x) := by
  obtain ⟨s,hs⟩ := exists_original_singleton_coordinate q k hk x hx
  refine ⟨s,?_⟩
  change imageAction q s=matrixAction (q.Extension 2)
    (positiveInclusion (q.Extension 2) (rootLinePositive (q.Extension 2) k x))
  rw [rootLinePositive_matrix]
  exact hs

theorem paired_positive_witness (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val≠k.val) (x : RootLine (q.Extension 2) k.val) :
    ∃s : Fixed q,imageAction q s=positiveAction (q.Extension 2)
      (rootLinePositive (q.Extension 2) k x*
        positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
          (rootLinePositive (q.Extension 2) k x)) := by
  obtain ⟨s,hs⟩ := exists_original_paired_coordinate q k hk x
  refine ⟨s,?_⟩
  change imageAction q s=matrixAction (q.Extension 2) (positiveInclusion (q.Extension 2)
    (rootLinePositive (q.Extension 2) k x*
      positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
        (rootLinePositive (q.Extension 2) k x)))
  rw [map_mul,positiveInclusion_twist,rootLinePositive_matrix]
  exact hs

theorem paired_positive_fixed (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val≠k.val) (x : RootLine (q.Extension 2) k.val) :
    positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (rootLinePositive (q.Extension 2) k x*
        positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
          (rootLinePositive (q.Extension 2) k x))=
      rootLinePositive (q.Extension 2) k x*
        positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
          (rootLinePositive (q.Extension 2) k x) := by
  obtain ⟨s,hs⟩ := paired_positive_witness q k hk x
  exact positive_fixed_of_original_witness q _ s hs

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveCoordinateLifts
