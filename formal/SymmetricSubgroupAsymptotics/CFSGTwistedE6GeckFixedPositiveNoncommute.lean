import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSingletonDerivedSeeds
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveActionInjective
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAdjacentLeadingNoncommute

/-! The two genuine singleton fixed positive roots at parameter one
have noncommuting actions on the SAME original image in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveNoncommute
open CFSGTwistedE6GeckSingletonDerivedSeeds CFSGTwistedE6GeckPositiveActionInjective
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6FixedA2 CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoCoordinateAdjacentLeadingNoncommute

def singletonPositive (K : Type) [Field K] (j : Fin 2) (a : K) : Positive K :=
  positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (node j) a

theorem singletonPositive_action (q : CFSG.PrimePower) (j : Fin 2) :
    imageAction q (root q false j 1 (one_fixed q))=
      positiveAction (q.Extension 2) (singletonPositive (q.Extension 2) j 1) := by
  rw [singleton_root_action]
  rfl

theorem singletonPositive_leading (K : Type) [Field K] (j : Fin 2) (a : K) :
    leadingCoordinates CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (singletonPositive K j a).val=
        (Pi.single (node j) a : Fin 6→K) :=
  congrArg (fun z : Multiplicative (Fin 6→K)=>z.toAdd)
    (leadingHom_positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (node j) a)

local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

theorem singleton_fixed_actions_not_commute (q : CFSG.PrimePower) :
    ¬Commute (imageAction q (root q false 0 1 (one_fixed q)))
      (imageAction q (root q false 1 1 (one_fixed q))) := by
  have hn := adjacent_leading_not_commute CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (q.Extension 2)
    (singletonPositive (q.Extension 2) 0 1) (singletonPositive (q.Extension 2) 1 1)
    (node 0) (node 1) 1 1 node_edge one_ne_zero one_ne_zero
    (singletonPositive_leading (q.Extension 2) 0 1) (singletonPositive_leading (q.Extension 2) 1 1)
  intro hc
  rw [singletonPositive_action,singletonPositive_action] at hc
  apply hn
  change singletonPositive (q.Extension 2) 0 1*singletonPositive (q.Extension 2) 1 1=
    singletonPositive (q.Extension 2) 1 1*singletonPositive (q.Extension 2) 0 1
  apply positiveAction_injective (q.Extension 2) q.prime
  simpa only [map_mul] using hc.eq

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveNoncommute
