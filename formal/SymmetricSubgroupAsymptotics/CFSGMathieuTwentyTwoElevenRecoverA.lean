import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
import Mathlib.Tactic.FinCases

/-! One selected twelve-letter recovery word, checked at all22 actual
points. The primary diagnostic supplied data only; this proof checks the
same pinned permutations and the displayed Lean multiplication order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
open CFSG.Models.Mathieu22Construction

theorem recoverA_eq : recoverA firstWord secondWord=a := by
  ext i
  fin_cases i <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
