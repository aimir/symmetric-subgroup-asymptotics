import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckActionRangeTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveQuotientInjectivity
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckImageWeylWitness
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! The SAME original-image action is injective on the actual E6 upper
root group. Consequently an original fixed-source action representing an
upper element forces that matrix element to be fixed. This uses the
proved positive-quotient theorem, not faithfulness of the original source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveActionInjective
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckActionRangeTwist CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckMatrixActionCovariance
open CFSGTwistedE6GeckSourceActionCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSerreQuadraticMatrix
open CFSGExceptionalGeckIntegralData
open CFSGTwistedE6GeckImageSemilinearTwist CFSGTwistedE6FixedA2
open CFSGSerreOrdinaryTwists

def positiveInclusion (K : Type) [Field K] : Positive K →* MatrixGroup K :=
  CFSGNormTwoCoordinatePositiveQuotientInjectivity.positiveInclusion
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K

theorem positiveInclusion_val (K : Type) [Field K] (u : Positive K) :
    (positiveInclusion K u).val=u.val := rfl

def positiveAction (K : Type) [Field K] : Positive K →* (Image K≃ₗ[K]Image K) :=
  (matrixAction K).comp (positiveInclusion K)

theorem raw_weyl_not_center (K : Type) [Field K] (i : Fin 6) :
    CFSGNormTwoGeckImageWeylWitness.weylElement CartanMatrix.E₆
      CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K i ∉
        Subgroup.center (MatrixGroup K) := by
  intro hc
  let f := CFSGNormTwoGeckImageWeylWitness.imageAction CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index E6_simple_sign K
  have hm := CFSGSimpleProjectiveDescent.map_mem_center
    f.rangeRestrict f.rangeRestrict_surjective _ hc
  exact CFSGNormTwoGeckImageWeylWitness.imageWeyl_not_center CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index E6_simple_sign K i hm

theorem actionRange_nontrivial (K : Type) [Field K] : Nontrivial (ActionRange K) := by
  let w : MatrixGroup K := CFSGNormTwoGeckImageWeylWitness.weylElement
    CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K 0
  have hne : matrixRangeProjection K w≠1 := by
    intro h
    exact raw_weyl_not_center K 0 (matrixRangeProjection_kernel_le_center K h)
  exact ⟨⟨matrixRangeProjection K w,1,hne⟩⟩

theorem positiveAction_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Function.Injective (positiveAction K) := by
  letI : Nontrivial (ActionRange K) := actionRange_nontrivial K
  have hi := CFSGNormTwoCoordinatePositiveQuotientInjectivity.positive_quotient_injective
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K p
    (matrixRangeProjection K) (matrixRangeProjection_surjective K)
  intro u v huv
  apply hi
  apply Subtype.ext
  exact huv

theorem positiveInclusion_twist (K : Type) [Field K] (sigma : K≃+*K) (u : Positive K) :
    positiveInclusion K (positiveTwist K sigma u)=
      matrixGroupTwist K sigma (positiveInclusion K u) := rfl

theorem positiveAction_twist (K : Type) [Field K] (sigma : K≃+*K) (u : Positive K) :
    positiveAction K (positiveTwist K sigma u)=imageAmbientTwist K sigma (positiveAction K u) := by
  change matrixAction K (positiveInclusion K (positiveTwist K sigma u))=_
  rw [positiveInclusion_twist,←matrix_action_covariance]
  rfl

local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

theorem positive_fixed_of_original_witness (q : CFSG.PrimePower)
    (u : Positive (q.Extension 2)) (s : Fixed q)
    (hs : imageAction q s=positiveAction (q.Extension 2) u) :
    positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) u=u := by
  apply positiveAction_injective (q.Extension 2) q.prime
  rw [positiveAction_twist,←hs,original_fixed_action_twist]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveActionInjective
