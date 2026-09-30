import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3ExceptionalInterface
import SymmetricSubgroupAsymptotics.T1RelativeClosure

/-!
# T1 from the mixed ordinary/rank-tail pre-E7 cover

The three special binary-rank families are source-summed before physical
pointing.  This file records the resulting final T1 and `AllTargets` boundary.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open Non2UnipotentPrefixFiniteMenu

theorem T1_of_preE7_noPairNoC3_localExceptional_data
    {r : ℕ}
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (D : PreE7NoPairNoC3LocalExceptionalData r)
    (Numerics : PreE7NoPairNoC3LocalExceptionalNumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) : T1 :=
  T1_of_preE7_noPairNoC3_estimate hTracey hExceptional hChief hWeight
    hPrimitive h18 hKP
    (preE7NoPairNoC3_exponentialForwardEstimate_of_localExceptionalData
      D Numerics hcoarse)

theorem allTargets_of_preE7_noPairNoC3_localExceptional_data
    {r : ℕ}
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (D : PreE7NoPairNoC3LocalExceptionalData r)
    (Numerics : PreE7NoPairNoC3LocalExceptionalNumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_preE7_noPairNoC3_localExceptional_data hTracey hExceptional
      hChief hWeight hPrimitive h18 hKP D Numerics hcoarse)

end SymmetricSubgroupAsymptotics

end
