import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorus
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeTorus
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelope

/-! Compatible scalar tuples give actual torus words in the SAME fixed
root-generated group J. Both literal fixed upper subgroups are normalized,
and the projected words therefore stabilize both original Sylow groups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeProductTorus
open CFSGE6GeckProductTorus CFSGE6GeckRelativeScalarCoordinates
open CFSGE6GeckRelativeScalarTuples CFSGTwistedE6GeckRelativeTorus
open CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGTwistedE6GeckNormalizerEnvelope
open CFSGE6GeckPairedParameterizedWeyl CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6FixedA2 CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckBorelNormalization CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSerreOrdinaryTwists
open CFSGCentralTwistedCommutatorLift CFSGNormTwoCoordinateRootLineNormalizers
open CFSGTwistedE6GeckRootGeneratedPGroup

def relativeTorusWord (q : CFSG.PrimePower)
    (x : relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  pairedTorusGenerated q 0 (x.val 0)*
    (pairedTorusGenerated q 1 (x.val 2)*
      (singletonTorusGenerated q 0 (fixedScalar _ _ x 1 (by decide))*
        singletonTorusGenerated q 1 (fixedScalar _ _ x 3 (by decide))))

theorem relativeTorusWord_val (q : CFSG.PrimePower)
    (x : relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)) :
    (relativeTorusWord q x).val=rawProductTorus (q.Extension 2) x.val := by
  change (pairedTorusGenerated q 0 (x.val 0)).val*
    ((pairedTorusGenerated q 1 (x.val 2)).val*
      ((singletonTorusGenerated q 0 (fixedScalar _ _ x 1 (by decide))).val*
        (singletonTorusGenerated q 1 (fixedScalar _ _ x 3 (by decide))).val))=_
  rw [pairedTorusGenerated_val,pairedTorusGenerated_val,
    singletonTorusGenerated_val,singletonTorusGenerated_val]
  have h1 : coefficientUnit q (fixedScalar _ _ x 1 (by decide))=x.val 1 :=
    fixedScalar_inclusion _ _ x 1 (by decide)
  have h3 : coefficientUnit q (fixedScalar _ _ x 3 (by decide))=x.val 3 :=
    fixedScalar_inclusion _ _ x 3 (by decide)
  rw [h1,h3]
  exact (rawProductTorus_orbit_factors _ _ x).symm

def relativeProductTorus (q : CFSG.PrimePower) :
    relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)→*
      fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  ((rawProductTorus (q.Extension 2)).comp
    (relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)).subtype).codRestrict _
      (fun x => by
        change rawProductTorus (q.Extension 2) x.val∈_
        rw [←relativeTorusWord_val q x]
        exact (relativeTorusWord q x).property)

@[simp] theorem relativeProductTorus_val (q : CFSG.PrimePower)
    (x : relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)) :
    (relativeProductTorus q x).val=rawProductTorus (q.Extension 2) x.val := rfl

theorem relativeProductTorus_normalizes (q : CFSG.PrimePower)
    (x : relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)) (neg : Bool) :
    relativeProductTorus q x∈Subgroup.normalizer
      (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) neg :
        Set (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))) := by
  let K := q.Extension 2
  let sigma := definingFieldAutomorphism q 2
  let J := fixedRootGenerated K sigma
  let t := relativeProductTorus q x
  have ht : t.val∈Subgroup.normalizer (signedFixed K sigma neg : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
    apply Subgroup.inf_normalizer_le_normalizer_inf
    refine ⟨?_,?_⟩
    · change t.val∈Subgroup.normalizer (SignedUpper K neg : Set (Matrix GeckIndex GeckIndex K)ˣ)
      have htorus := rawProductTorus_mem_torus K x.val
      rw [←relativeProductTorus_val q x] at htorus
      exact torusGroup_normalizes CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K neg htorus
    · exact (fixedSubgroup (unitTwist K sigma)).le_normalizer
        (fixedRootGenerated_le_fixed K sigma t.property)
  exact Subgroup.le_normalizer_comap J.subtype ht

def originalProductTorus (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)→*CFSG.Models.TwistedE6 q :=
  (generatedToOriginal q).comp (relativeProductTorus q)

theorem originalProductTorus_normalizes (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (x : relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)) (neg : Bool) :
    originalProductTorus q x∈Subgroup.normalizer
      ((rootPart (q.Extension 2) (definingFieldAutomorphism q 2) neg).map (generatedToOriginal q) :
        Set (CFSG.Models.TwistedE6 q)) :=
  Subgroup.le_normalizer_map (generatedToOriginal q)
    ⟨relativeProductTorus q x,relativeProductTorus_normalizes q x neg,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeProductTorus
