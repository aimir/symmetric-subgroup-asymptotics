import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedMatrixActions
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSingletonDerivedSeeds
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveActionInjective
import SymmetricSubgroupAsymptotics.CFSGFFourE6RegularPositive

/-! The literal E6 upper word at all six simple parameters one is the
action of an ORIGINAL twisted-E6 fixed word. Upper-action injectivity
proves it matrix-twist fixed; its six leading coordinates are one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRegularFixedPositive
open CFSGTwistedE6GeckPairedMatrixActions CFSGTwistedE6GeckSingletonDerivedSeeds
open CFSGTwistedE6GeckPositiveActionInjective CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckSourceWordAction CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6FixedA2 CFSGTwistedE6PairedFixedRoots CFSGSerreOrdinaryTwists
open CFSGSerreQuadraticMatrix

abbrev regularPositive (K : Type) [Field K] : Positive K :=
  CFSGFFourE6RegularPositive.regularPositive K

def regularSource (q : CFSG.PrimePower) : Fixed q :=
  pairedRoot q false 0 1*pairedRoot q false 1 1*
    root q false 1 1 (one_fixed q)*root q false 0 1 (one_fixed q)

def regularMatrixWord (q : CFSG.PrimePower) : MatrixGroup (q.Extension 2) :=
  matrixPairedRoot q 0 1*matrixPairedRoot q 1 1*
    matrixSingletonRoot q false 1 1*matrixSingletonRoot q false 0 1

theorem regularMatrixWord_eq_positive (q : CFSG.PrimePower) :
    regularMatrixWord q=positiveInclusion (q.Extension 2) (regularPositive (q.Extension 2)) := by
  apply Subtype.ext
  change (canonicalRoot rawData (q.Extension 2) false 0 1*
      canonicalRoot rawData (q.Extension 2) false 5 (1^q.order))*
      (canonicalRoot rawData (q.Extension 2) false 2 1*
        canonicalRoot rawData (q.Extension 2) false 4 (1^q.order))*
      canonicalRoot rawData (q.Extension 2) false 3 1*
      canonicalRoot rawData (q.Extension 2) false 1 1=
    canonicalRoot rawData (q.Extension 2) false 0 1*
      canonicalRoot rawData (q.Extension 2) false 5 1*
      canonicalRoot rawData (q.Extension 2) false 2 1*
      canonicalRoot rawData (q.Extension 2) false 4 1*
      canonicalRoot rawData (q.Extension 2) false 3 1*
      canonicalRoot rawData (q.Extension 2) false 1 1
  simp only [one_pow,mul_assoc]

theorem regularSource_action (q : CFSG.PrimePower) :
    imageAction q (regularSource q)=positiveAction (q.Extension 2) (regularPositive (q.Extension 2)) := by
  calc
    _ = matrixAction (q.Extension 2) (regularMatrixWord q) := by
      simp only [regularSource,regularMatrixWord,map_mul,paired_root_action,singleton_root_action]
    _ = _ := by rw [regularMatrixWord_eq_positive];rfl

theorem regularPositive_fixed (q : CFSG.PrimePower) :
    positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (regularPositive (q.Extension 2))=regularPositive (q.Extension 2) :=
  positive_fixed_of_original_witness q _ (regularSource q) (regularSource_action q)

def regularMatrix (K : Type) [Field K] : MatrixGroup K := positiveInclusion K (regularPositive K)

theorem regularMatrix_positive (K : Type) [Field K] : (regularMatrix K).val∈Positive K :=
  (regularPositive K).property

theorem regularMatrix_fixed (q : CFSG.PrimePower) :
    matrixGroupTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (regularMatrix (q.Extension 2))=regularMatrix (q.Extension 2) := by
  change matrixGroupTwist (q.Extension 2) (definingFieldAutomorphism q 2)
    (positiveInclusion (q.Extension 2) (regularPositive (q.Extension 2)))=_
  rw [←positiveInclusion_twist,regularPositive_fixed]
  rfl

theorem regularMatrix_leading (K : Type) [Field K] (i : Fin 6) :
    CFSGNormTwoCoordinateLeadingFactor.leadingCoordinates CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose CFSGExceptionalCartanPositiveDefinite.E6_positive_definite
      CartanMatrix.E₆_off_diag_nonpos K (regularMatrix K).val i≠0 := by
  change CFSGNormTwoCoordinateLeadingFactor.leadingCoordinates CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose CFSGExceptionalCartanPositiveDefinite.E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos K (regularPositive K).val i≠0
  rw [CFSGFFourE6RegularPositive.regularPositive_leading]
  exact one_ne_zero

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRegularFixedPositive
