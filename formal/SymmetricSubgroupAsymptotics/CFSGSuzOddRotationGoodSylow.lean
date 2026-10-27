import SymmetricSubgroupAsymptotics.CFSGMatrixOddRotationBinaryFrames
import SymmetricSubgroupAsymptotics.CFSGSuzOddRotationBrayMatrixIdentities

/-! Good Sylow two for the SAME pinned Suz64/F3 matrix-fibre closure.
All four required WHOLE positive-matrix power equations come from the
imported certificate leaf. No power premise remains at this endpoint. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzOddRotationGoodSylow
open CFSG.Models.MatrixGroups.Suz CFSGReduction

theorem goodSylowPrime (hCFSG : CFSG.CFSGClassification)
    [Finite Model] (hn : ¬IsMulCommutative Model) : GoodSylowPrime Model 2 := by
  exact CFSGMatrixOddRotationBinaryFrames.matrix_model_goodSylowTwo_of_odd_rotation
    hCFSG 3 64 rows1 rows2 hn 7 8
    CFSGSuzOddRotationBrayMatrixIdentities.first_square
    CFSGSuzOddRotationBrayMatrixIdentities.second_cube
    (by simpa only [show 2*7+1=(15 : ℕ) by decide] using
      CFSGSuzOddRotationBrayMatrixIdentities.rotation_fifteenth)
    (by simpa only [show 7+1=(8 : ℕ) by decide,show 2^8=(256 : ℕ) by decide] using
      CFSGSuzOddRotationBrayMatrixIdentities.bray_binary_power)

end SymmetricSubgroupAsymptotics.CFSGSuzOddRotationGoodSylow
