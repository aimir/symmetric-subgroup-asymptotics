import SymmetricSubgroupAsymptotics.BinaryNativeRecurrence
import SymmetricSubgroupAsymptotics.Non2PreE7ResidualPairPartition
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairConcreteInterface
import SymmetricSubgroupAsymptotics.Non2PreE7C3Partition

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

/-- Concrete non-pair owner, retained-cell, and numerical packages close T1
through the already proved binary, post-E7, and residual-pair estimates. -/
theorem T1_of_preE7_nonPair_data
    {r : ℕ}
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (D : PreE7NonPairOwnerComparatorData r)
    (Cells : PreE7NonPairRetainedCellData D)
    (Numerics : PreE7NonPairNumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) : T1 :=
  T1_of_preE7_nonPair_estimate hTracey hExceptional
    (preE7NonPair_exponentialForwardEstimate_of_data
      D Cells Numerics hcoarse)

/-- The same concrete non-pair packages close all three approved targets. -/
theorem allTargets_of_preE7_nonPair_data
    {r : ℕ}
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (D : PreE7NonPairOwnerComparatorData r)
    (Cells : PreE7NonPairRetainedCellData D)
    (Numerics : PreE7NonPairNumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_preE7_nonPair_data
      hTracey hExceptional D Cells Numerics hcoarse)

/-- After the complete regular-C3 family is also paid, an estimate for the
exact remaining complement closes T1. -/
theorem T1_of_preE7_noPairNoC3_estimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio) : T1 :=
  T1_of_preE7_nonPair_estimate hTracey hExceptional
    (preE7NonPair_exponentialForwardEstimate_of_noC3
      hChief hWeight hPrimitive h18 hKP P)

/-- The exact complement after the pair and regular-C3 cuts closes all three
approved targets. -/
theorem allTargets_of_preE7_noPairNoC3_estimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_preE7_noPairNoC3_estimate hTracey hExceptional
      hChief hWeight hPrimitive h18 hKP P)

end SymmetricSubgroupAsymptotics

end
