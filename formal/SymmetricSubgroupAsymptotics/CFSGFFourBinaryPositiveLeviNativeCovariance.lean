import SymmetricSubgroupAsymptotics.CFSGFFourBinaryNativeCentralAction

/-! Actual positive F4 Levi parameters lift the displayed native positive
C3 actions on the SAME central chart. No lift of arbitrary native
symplectic elements is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryPositiveLeviNativeCovariance
open CFSGFFourBinaryNativeCentralAction CFSGFFourBinaryLeviNativeVectorCoordinates
open CFSGFFourBinaryShortLeviCentralAction CFSGFFourBinaryLongLeviCentralAction
open CFSGFFourBinaryRadicalCentralLayers CFSGFFourBinaryCentralCoordinateWords
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
local instance fFourPositiveNativeCovarianceRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

theorem positive_central_covariance (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K=2) (i : Fin 3) (a : K) (x : CentralCoordinates K) :
    canonicalRoot realizationData K false i.castSucc a * centralMatrixHom K x *
        (canonicalRoot realizationData K false i.castSucc a)⁻¹ =
      centralMatrixHom K (nativeCentralAction K hK (nativePositive K i a) x) := by
  fin_cases i
  · exact (short_positive_central_action K 0 a x).trans
      (congrArg (centralMatrixHom K) (nativeCentralAction_short K hK 0 a x).symm)
  · exact (short_positive_central_action K 1 a x).trans
      (congrArg (centralMatrixHom K) (nativeCentralAction_short K hK 1 a x).symm)
  · exact (long_positive_central_action K a x).trans
      (congrArg (centralMatrixHom K) (nativeCentralAction_long K hK a x).symm)

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryPositiveLeviNativeCovariance
