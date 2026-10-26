import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
import Mathlib.Tactic.FinCases

/-! One selected eleven-letter recovery word, checked at all22 actual
points. No full group table, closure enumeration, or diagnostic receipt
is used as proof evidence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
open CFSG.Models.Mathieu22Construction

theorem recoverB_eq : recoverB firstWord secondWord=b := by
  ext i
  fin_cases i <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
