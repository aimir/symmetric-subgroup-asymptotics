import SymmetricSubgroupAsymptotics.CFSGTwoBinaryPowerGenerators
import SymmetricSubgroupAsymptotics.CFSGONBinaryMatrixPowerIdentities

/-! SOURCE ONLY until the imported FULL original ON matrix identities pass.
No selected-row period is used as a whole-matrix order premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGONBinaryPowerGoodSylow
open CFSGReduction CFSG.Models.MatrixGroups.ON

theorem goodSylowPrime (hCFSG : CFSG.CFSGClassification)
    [Finite Model] (hn : ¬IsMulCommutative Model) : GoodSylowPrime Model 2 := by
  exact matrix_model_goodSylowTwo_of_binary_powers hCFSG 3 154 rows1 rows2 hn 1 2
    (by simpa only [show (2 : ℕ)^1 = 2 by decide] using
      CFSGONBinaryMatrixPowerIdentities.first_square)
    (by simpa only [show (2 : ℕ)^2 = 4 by decide] using
      CFSGONBinaryMatrixPowerIdentities.second_fourth)

end SymmetricSubgroupAsymptotics.CFSGONBinaryPowerGoodSylow
