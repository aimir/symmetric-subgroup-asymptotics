import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow0
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow1
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow2
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow3
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow4
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow5
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow6
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow7
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow8
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow9
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow10
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow11
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow12
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow13
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow14
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow15
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow16
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow17
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow18
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow19
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow20
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow21
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow22
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow23
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow24
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow25
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow26
import SymmetricSubgroupAsymptotics.CFSGRuFirstSquareRow27
import SymmetricSubgroupAsymptotics.CFSGRuSelectedSecondFourthRowPilot
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow1
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow2
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow3
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow4
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow5
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow6
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow7
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow8
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow9
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow10
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow11
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow12
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow13
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow14
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow15
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow16
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow17
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow18
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow19
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow20
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow21
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow22
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow23
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow24
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow25
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow26
import SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow27

/-! The two FULL identities for the SAME original binary28 matrices.
All arithmetic resides in separately checked selected-row modules.
This source assembles their exact rows by matrix extensionality only. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGRuBinaryMatrixPowerIdentities
open CFSG.Models.MatrixGroups.Ru

theorem first_square : CFSG.Models.MatrixData.matrix 2 28 rows1 ^ 2 = 1 := by
  ext i z
  fin_cases i
  · exact CFSGRuFirstSquareRow0.row_identity z
  · exact CFSGRuFirstSquareRow1.row_identity z
  · exact CFSGRuFirstSquareRow2.row_identity z
  · exact CFSGRuFirstSquareRow3.row_identity z
  · exact CFSGRuFirstSquareRow4.row_identity z
  · exact CFSGRuFirstSquareRow5.row_identity z
  · exact CFSGRuFirstSquareRow6.row_identity z
  · exact CFSGRuFirstSquareRow7.row_identity z
  · exact CFSGRuFirstSquareRow8.row_identity z
  · exact CFSGRuFirstSquareRow9.row_identity z
  · exact CFSGRuFirstSquareRow10.row_identity z
  · exact CFSGRuFirstSquareRow11.row_identity z
  · exact CFSGRuFirstSquareRow12.row_identity z
  · exact CFSGRuFirstSquareRow13.row_identity z
  · exact CFSGRuFirstSquareRow14.row_identity z
  · exact CFSGRuFirstSquareRow15.row_identity z
  · exact CFSGRuFirstSquareRow16.row_identity z
  · exact CFSGRuFirstSquareRow17.row_identity z
  · exact CFSGRuFirstSquareRow18.row_identity z
  · exact CFSGRuFirstSquareRow19.row_identity z
  · exact CFSGRuFirstSquareRow20.row_identity z
  · exact CFSGRuFirstSquareRow21.row_identity z
  · exact CFSGRuFirstSquareRow22.row_identity z
  · exact CFSGRuFirstSquareRow23.row_identity z
  · exact CFSGRuFirstSquareRow24.row_identity z
  · exact CFSGRuFirstSquareRow25.row_identity z
  · exact CFSGRuFirstSquareRow26.row_identity z
  · exact CFSGRuFirstSquareRow27.row_identity z

theorem second_fourth : CFSG.Models.MatrixData.matrix 2 28 rows2 ^ 4 = 1 := by
  ext i z
  fin_cases i
  · exact CFSGRuSelectedSecondFourthRowPilot.selected_fourth_power_row_identity z
  · exact CFSGRuSecondFourthRow1.row_identity z
  · exact CFSGRuSecondFourthRow2.row_identity z
  · exact CFSGRuSecondFourthRow3.row_identity z
  · exact CFSGRuSecondFourthRow4.row_identity z
  · exact CFSGRuSecondFourthRow5.row_identity z
  · exact CFSGRuSecondFourthRow6.row_identity z
  · exact CFSGRuSecondFourthRow7.row_identity z
  · exact CFSGRuSecondFourthRow8.row_identity z
  · exact CFSGRuSecondFourthRow9.row_identity z
  · exact CFSGRuSecondFourthRow10.row_identity z
  · exact CFSGRuSecondFourthRow11.row_identity z
  · exact CFSGRuSecondFourthRow12.row_identity z
  · exact CFSGRuSecondFourthRow13.row_identity z
  · exact CFSGRuSecondFourthRow14.row_identity z
  · exact CFSGRuSecondFourthRow15.row_identity z
  · exact CFSGRuSecondFourthRow16.row_identity z
  · exact CFSGRuSecondFourthRow17.row_identity z
  · exact CFSGRuSecondFourthRow18.row_identity z
  · exact CFSGRuSecondFourthRow19.row_identity z
  · exact CFSGRuSecondFourthRow20.row_identity z
  · exact CFSGRuSecondFourthRow21.row_identity z
  · exact CFSGRuSecondFourthRow22.row_identity z
  · exact CFSGRuSecondFourthRow23.row_identity z
  · exact CFSGRuSecondFourthRow24.row_identity z
  · exact CFSGRuSecondFourthRow25.row_identity z
  · exact CFSGRuSecondFourthRow26.row_identity z
  · exact CFSGRuSecondFourthRow27.row_identity z

end SymmetricSubgroupAsymptotics.CFSGRuBinaryMatrixPowerIdentities
