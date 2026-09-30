import SymmetricSubgroupAsymptotics.BinaryNativeRecurrence
import SymmetricSubgroupAsymptotics.Non2PreE7ResidualPairPartition

/-!
# The final relative closure of T1

The native binary recurrence is unconditional inside the project.  After the
post-`E7` outside sector is inserted, the sole remaining project estimate is
the forward estimate for the complementary pre-`E7` sector.  This file records
that exact boundary and performs the final assembly without introducing a new
counting premise.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open Non2UnipotentPrefixFiniteMenu

/-- The proved native binary recurrence, transported to the ambient-degree
frontier consumed by the ordinary-remainder assembly. -/
noncomputable def binaryFrontier_exponentialForwardEstimate :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      OrdinaryFrontierClosure.binaryFrontierRatio :=
  BinaryFrontierTransport.toAmbientEstimate
    BinaryNativeRecurrence.rankForwardEstimate

/-- A forward estimate for the exact pre-`E7` complement is the only remaining
project estimate needed for T1.  The two displayed Tracey hypotheses are the
named published inputs already used by the post-`E7` owner. -/
theorem T1_of_preE7_estimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7UnresolvedOutsideRatio) : T1 :=
  OrdinaryFrontierClosure.T1_of_frontier_estimates
    (outsideFrontier_exponentialForwardEstimate_of_preE7
      hTracey hExceptional P)
    binaryFrontier_exponentialForwardEstimate

/-- The same single pre-`E7` estimate closes all three approved targets. -/
theorem allTargets_of_preE7_estimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7UnresolvedOutsideRatio) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_preE7_estimate hTracey hExceptional P)

/-- After removing the four residual pair widths, a forward estimate for the
exact non-pair complement is the sole remaining input needed for T1. -/
theorem T1_of_preE7_nonPair_estimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NonPairResidualRatio) : T1 :=
  T1_of_preE7_estimate hTracey hExceptional
    (preE7Unresolved_exponentialForwardEstimate_of_nonPair
      hTracey hExceptional P)

/-- The exact non-pair pre-`E7` estimate closes all three approved targets. -/
theorem allTargets_of_preE7_nonPair_estimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NonPairResidualRatio) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_preE7_nonPair_estimate hTracey hExceptional P)

end SymmetricSubgroupAsymptotics

end
