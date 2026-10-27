import SymmetricSubgroupAsymptotics.CFSGMathieuTailPermutationExtension
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu22.Certificates.StabilizerChain
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu23.Certificates.StabilizerChain
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu24.Certificates.StabilizerChain

/-! Literal AST equality of the shared five-level tail. The valid slots
have sizes22,21,20,16,3, totaling82. Equalities below also include harmless
default words at invalid slots. No permutation value is re-enumerated:
word23_eval/word24_eval transport all actual seed values from degree22. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTailWordTransport
open CFSGMathieuTailPermutationExtension

theorem first_word23 (i : Fin 22) :
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.orbitZeroWord i).map letter23 =
      CFSG.Certificates.Mathieu23.M23Certificates.StabilizerChain.levelTwoWord
        (i.castLE (by decide : 22 ≤ 23)) := by
  fin_cases i <;> rfl

theorem second_word23 (i : Fin 22) :
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.zeroStabilizerWord i).map letter23 =
      CFSG.Certificates.Mathieu23.M23Certificates.StabilizerChain.levelThreeWord
        (i.castLE (by decide : 22 ≤ 23)) := by
  fin_cases i <;> rfl

theorem third_word23 (i : Fin 22) :
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.zeroOneStabilizerWord i).map letter23 =
      CFSG.Certificates.Mathieu23.M23Certificates.StabilizerChain.levelFourWord
        (i.castLE (by decide : 22 ≤ 23)) := by
  fin_cases i <;> rfl

theorem fourth_word23 (i : Fin 22) :
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.levelFourWord i).map letter23 =
      CFSG.Certificates.Mathieu23.M23Certificates.StabilizerChain.levelFiveWord
        (i.castLE (by decide : 22 ≤ 23)) := by
  fin_cases i <;> rfl

theorem fifth_word23 (i : Fin 22) :
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.levelFiveWord i).map letter23 =
      CFSG.Certificates.Mathieu23.M23Certificates.StabilizerChain.levelSixWord
        (i.castLE (by decide : 22 ≤ 23)) := by
  fin_cases i <;> rfl

theorem first_word24 (i : Fin 22) :
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.orbitZeroWord i).map letter24 =
      CFSG.Certificates.Mathieu24.M24Certificates.StabilizerChain.levelThreeWord
        (i.castLE (by decide : 22 ≤ 24)) := by
  fin_cases i <;> rfl

theorem second_word24 (i : Fin 22) :
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.zeroStabilizerWord i).map letter24 =
      CFSG.Certificates.Mathieu24.M24Certificates.StabilizerChain.levelFourWord
        (i.castLE (by decide : 22 ≤ 24)) := by
  fin_cases i <;> rfl

theorem third_word24 (i : Fin 22) :
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.zeroOneStabilizerWord i).map letter24 =
      CFSG.Certificates.Mathieu24.M24Certificates.StabilizerChain.levelFiveWord
        (i.castLE (by decide : 22 ≤ 24)) := by
  fin_cases i <;> rfl

theorem fourth_word24 (i : Fin 22) :
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.levelFourWord i).map letter24 =
      CFSG.Certificates.Mathieu24.M24Certificates.StabilizerChain.levelSixWord
        (i.castLE (by decide : 22 ≤ 24)) := by
  fin_cases i <;> rfl

theorem fifth_word24 (i : Fin 22) :
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.levelFiveWord i).map letter24 =
      CFSG.Certificates.Mathieu24.M24Certificates.StabilizerChain.levelSevenWord
        (i.castLE (by decide : 22 ≤ 24)) := by
  fin_cases i <;> rfl

end SymmetricSubgroupAsymptotics.CFSGMathieuTailWordTransport
