import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRowZeroPilot
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153
import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRow1
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145
import SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153

/-! FULL original ON matrix identities, assembled only after all308
actual row links passed. Matrix extensionality, no new arithmetic and
no assumption of whole-matrix orders from selected-row periods. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGONBinaryMatrixPowerIdentities
open CFSG.Models.MatrixGroups.ON

theorem first_square : CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2 = 1 := by
  ext i z
  fin_cases i
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRowZeroPilot.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row1.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row2.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row3.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row4.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row5.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row6.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row7.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row8.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row9.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row10.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row11.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row12.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row13.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row14.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row15.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16.Row16.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row17.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row18.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row19.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row20.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row21.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row22.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row23.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row24.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row25.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row26.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row27.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row28.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row29.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row30.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row31.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32.Row32.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row33.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row34.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row35.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row36.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row37.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row38.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row39.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row40.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row41.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row42.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row43.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row44.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row45.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row46.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row47.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48.Row48.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row49.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row50.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row51.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row52.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row53.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row54.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row55.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row56.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row57.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row58.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row59.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row60.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row61.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row62.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row63.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows49Through64.Row64.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row65.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row66.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row67.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row68.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row69.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row70.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row71.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row72.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row73.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row74.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row75.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row76.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row77.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row78.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row79.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows65Through80.Row80.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row81.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row82.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row83.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row84.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row85.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row86.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row87.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row88.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row89.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row90.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row91.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row92.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row93.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row94.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row95.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows81Through96.Row96.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row97.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row98.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row99.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row100.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row101.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row102.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row103.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row104.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row105.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row106.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row107.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row108.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row109.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row110.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row111.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows97Through112.Row112.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row113.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row114.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row115.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row116.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row117.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row118.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row119.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row120.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row121.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row122.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row123.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row124.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row125.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row126.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row127.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128.Row128.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row129.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row130.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row131.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row132.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row133.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row134.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row135.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row136.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row137.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row138.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row139.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row140.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row141.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row142.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row143.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows129Through144.Row144.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153.Row145.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153.Row146.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153.Row147.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153.Row148.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153.Row149.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153.Row150.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153.Row151.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153.Row152.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153.Row153.row_identity z

theorem second_fourth : CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4 = 1 := by
  ext i z
  fin_cases i
  · exact SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot.selected_fourth_power_row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRow1.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row2.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row3.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row4.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row5.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row6.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row7.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row8.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row9.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row10.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row11.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row12.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row13.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row14.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row15.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row16.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen.Row17.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row18.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row19.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row20.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row21.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row22.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row23.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row24.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row25.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row26.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row27.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row28.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row29.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row30.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row31.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row32.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows18Through33.Row33.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row34.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row35.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row36.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row37.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row38.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row39.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row40.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row41.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row42.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row43.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row44.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row45.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row46.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row47.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row48.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows34Through49.Row49.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row50.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row51.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row52.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row53.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row54.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row55.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row56.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row57.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row58.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row59.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row60.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row61.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row62.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row63.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row64.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65.Row65.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row66.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row67.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row68.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row69.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row70.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row71.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row72.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row73.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row74.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row75.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row76.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row77.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row78.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row79.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row80.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows66Through81.Row81.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row82.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row83.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row84.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row85.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row86.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row87.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row88.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row89.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row90.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row91.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row92.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row93.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row94.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row95.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row96.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows82Through97.Row97.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row98.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row99.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row100.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row101.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row102.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row103.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row104.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row105.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row106.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row107.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row108.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row109.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row110.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row111.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row112.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows98Through113.Row113.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row114.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row115.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row116.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row117.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row118.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row119.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row120.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row121.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row122.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row123.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row124.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row125.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row126.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row127.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row128.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows114Through129.Row129.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row130.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row131.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row132.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row133.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row134.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row135.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row136.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row137.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row138.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row139.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row140.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row141.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row142.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row143.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row144.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows130Through145.Row145.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153.Row146.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153.Row147.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153.Row148.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153.Row149.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153.Row150.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153.Row151.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153.Row152.row_identity z
  · exact SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153.Row153.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONBinaryMatrixPowerIdentities
