import SymmetricSubgroupAsymptotics.CFSGCoTwoSelectedWordTwentyThreeTrajectory
import Mathlib.Tactic.FinCases

/-! Actual OLD Co2 prime23 divisor; no order/recognition premise remains. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoSelectedWordTwentyThreePrimeDivisor
open CFSGCoTwoLiteralRepresentation CFSGCoTwoNativeTwentyTwoRelatorIdentities
theorem twentyThree_dvd_card [Finite CFSG.Models.Presentations.Co2.Model] :
    23 ∣ Nat.card CFSG.Models.Presentations.Co2.Model :=
  twentyThree_dvd_card_of_selected_period relatorPacket
    (CFSGCoTwoSelectedWordTwentyThreeTrajectory.vectors 0) CFSGCoTwoSelectedWordTwentyThreeTrajectory.return_twentyThree
    CFSGCoTwoSelectedWordTwentyThreeTrajectory.nonreturn_one

end SymmetricSubgroupAsymptotics.CFSGCoTwoSelectedWordTwentyThreePrimeDivisor
