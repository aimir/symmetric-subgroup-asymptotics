import SymmetricSubgroupAsymptotics.CFSGTwoBinaryPowerGenerators
import SymmetricSubgroupAsymptotics.CFSGRuBinaryMatrixPowerIdentities

/-! Good Sylow two for the SAME original raw binary28 Ru model.
The two FULL literal matrix identities are proved by the imported row
certificates and their matrix assembly, not assumed at this endpoint.
Pinned CFSG supplies odd-order solvability in Sylow-two normalizers.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGRuBinaryPowerGoodSylow
open CFSGReduction CFSG.Models.MatrixGroups.Ru

theorem goodSylowPrime (hCFSG : CFSG.CFSGClassification)
    [Finite Model] (hn : ¬IsMulCommutative Model) : GoodSylowPrime Model 2 := by
  exact matrix_model_goodSylowTwo_of_binary_powers hCFSG 2 28 rows1 rows2 hn 1 2
    (by simpa only [show (2 : ℕ)^1 = 2 by decide] using
      CFSGRuBinaryMatrixPowerIdentities.first_square)
    (by simpa only [show (2 : ℕ)^2 = 4 by decide] using
      CFSGRuBinaryMatrixPowerIdentities.second_fourth)

end SymmetricSubgroupAsymptotics.CFSGRuBinaryPowerGoodSylow
