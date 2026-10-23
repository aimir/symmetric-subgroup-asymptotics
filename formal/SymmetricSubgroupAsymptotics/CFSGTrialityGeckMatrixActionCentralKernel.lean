import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceWordAction
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceImageRange
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRawActionKernel
import SymmetricSubgroupAsymptotics.CFSGSubmoduleActionKernelTransport

/-! The actual matrix action on the SAME source-Cartan-transported
triality image has central kernel. The already proved raw quartic kernel
theorem is reused via equality of the literal image submodules. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixActionCentralKernel
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4NormTwo CFSGSerreQuadraticMatrix CFSGTrialityGeckRootAction
open CFSGTrialityGeckRawActionKernel

theorem image_ranges_equal (K : Type) [Field K] :
    (baseChange data K).range = (baseChange rawData K).range :=
  transportSource_baseChange_range_eq cartan_eq rawData K

theorem matrixAction_kernel_le_raw (K : Type) [Field K] :
    (matrixAction K).ker ≤ (rawAction K).ker :=
  CFSGSubmoduleActionKernelTransport.kernel_le_of_shared_values
    (baseChange data K).range (baseChange rawData K).range (image_ranges_equal K)
    (matrixAction K) (rawAction K)
    (fun g y => (g.val : Matrix GeckIndex GeckIndex K) * y *
      (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K))
    (matrixAction_apply K) (rawAction_apply K)

theorem matrixAction_kernel_le_center (K : Type) [Field K] :
    (matrixAction K).ker ≤ Subgroup.center (MatrixGroup K) :=
  (matrixAction_kernel_le_raw K).trans (rawAction_kernel_le_center K)

theorem matrixRangeProjection_kernel_le_center (K : Type) [Field K] :
    (matrixAction K).rangeRestrict.ker ≤ Subgroup.center (MatrixGroup K) := by
  intro g hg
  exact matrixAction_kernel_le_center K (congrArg Subtype.val hg)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixActionCentralKernel
