import SymmetricSubgroupAsymptotics.Non2PreE7JointTopYonedaIncidence
import SymmetricSubgroupAsymptotics.T1RelativeClosure

/-!
# T1 from joint terminal top/Yoneda cells

This file states the final theorem boundary after the terminal residual has
been upgraded from fixed-top cells to a joint weighted top/Yoneda incidence.
All structural information is supplied by
`PreE7ResidualJointTopCellSourceData`; all remaining exponent and menu sums
are supplied by the existing additive numerical certificate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open Non2UnipotentPrefixFiniteMenu

/-- Joint terminal top/Yoneda cells, together with the existing numerical
certificate and named published inputs, close the principal asymptotic
theorem. -/
theorem T1_of_preE7_noPairNoC3_jointTopCell_data
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7ResidualJointTopCellSourceData w U)
    (Numerics : PreE7NoPairNoC3LocalAdditiveNumericalCertificate
      (preE7NoPairNoC3_localAdditiveAxisData_of_residualJointTopCells D))
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) : T1 :=
  T1_of_preE7_noPairNoC3_localAdditive_data
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP
    (preE7NoPairNoC3_localAdditiveAxisData_of_residualJointTopCells D)
    Numerics hcoarse

/-- The same joint terminal construction closes all three approved theorem
statements through the already proved implications from `T1`. -/
theorem allTargets_of_preE7_noPairNoC3_jointTopCell_data
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7ResidualJointTopCellSourceData w U)
    (Numerics : PreE7NoPairNoC3LocalAdditiveNumericalCertificate
      (preE7NoPairNoC3_localAdditiveAxisData_of_residualJointTopCells D))
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    AllTargets :=
  allTargets_of_preE7_noPairNoC3_localAdditive_data
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP
    (preE7NoPairNoC3_localAdditiveAxisData_of_residualJointTopCells D)
    Numerics hcoarse

end SymmetricSubgroupAsymptotics

end
