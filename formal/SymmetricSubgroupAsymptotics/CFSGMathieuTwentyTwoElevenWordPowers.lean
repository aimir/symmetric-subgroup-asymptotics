import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
import Mathlib.Tactic.FinCases

/-! The WHOLE selected permutation has eleventh power one, checked at
every original point. The old point-zero period theorem alone did not
provide this identity. The conjugate word inherits the same period. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
open CFSG.Models.Mathieu22Construction

theorem firstWord_pow_eleven : firstWord^11=1 := by
  ext i
  fin_cases i <;> decide +kernel

theorem secondWord_pow_eleven : secondWord^11=1 := by
  have he : secondWord=MulAut.conj a firstWord := rfl
  rw [he,←map_pow,firstWord_pow_eleven,map_one]

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
