import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceFirstStep

/-! The remaining thirteen applications of the SAME selected Co3 a*b/e0
trace. Every fixed matrix-vector transition is checked in its own bounded
declaration; the two uniform endpoints only assemble these declarations.
No other word, vector, model, matrix power or closure is evaluated. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceTransitions
open CFSGCoThreeSelectedTraceData CFSGCoThreeSelectedTraceFirstStep

private theorem b_step_1 : b *ᵥ vectors 1 = afterB 1 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_1 : a *ᵥ afterB 1 = vectors 2 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_2 : b *ᵥ vectors 2 = afterB 2 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_2 : a *ᵥ afterB 2 = vectors 3 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_3 : b *ᵥ vectors 3 = afterB 3 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_3 : a *ᵥ afterB 3 = vectors 4 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_4 : b *ᵥ vectors 4 = afterB 4 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_4 : a *ᵥ afterB 4 = vectors 5 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_5 : b *ᵥ vectors 5 = afterB 5 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_5 : a *ᵥ afterB 5 = vectors 6 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_6 : b *ᵥ vectors 6 = afterB 6 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_6 : a *ᵥ afterB 6 = vectors 7 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_7 : b *ᵥ vectors 7 = afterB 7 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_7 : a *ᵥ afterB 7 = vectors 8 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_8 : b *ᵥ vectors 8 = afterB 8 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_8 : a *ᵥ afterB 8 = vectors 9 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_9 : b *ᵥ vectors 9 = afterB 9 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_9 : a *ᵥ afterB 9 = vectors 10 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_10 : b *ᵥ vectors 10 = afterB 10 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_10 : a *ᵥ afterB 10 = vectors 11 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_11 : b *ᵥ vectors 11 = afterB 11 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_11 : a *ᵥ afterB 11 = vectors 12 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_12 : b *ᵥ vectors 12 = afterB 12 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_12 : a *ᵥ afterB 12 = vectors 13 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem b_step_13 : b *ᵥ vectors 13 = afterB 13 := by
  funext j
  fin_cases j <;> decide +kernel

private theorem a_step_13 : a *ᵥ afterB 13 = vectors 14 := by
  funext j
  fin_cases j <;> decide +kernel

theorem b_step (i : Fin 14) : b *ᵥ vectors i.castSucc = afterB i := by
  fin_cases i
  · exact b_first
  · exact b_step_1
  · exact b_step_2
  · exact b_step_3
  · exact b_step_4
  · exact b_step_5
  · exact b_step_6
  · exact b_step_7
  · exact b_step_8
  · exact b_step_9
  · exact b_step_10
  · exact b_step_11
  · exact b_step_12
  · exact b_step_13

theorem a_step (i : Fin 14) : a *ᵥ afterB i = vectors i.succ := by
  fin_cases i
  · exact a_first
  · exact a_step_1
  · exact a_step_2
  · exact a_step_3
  · exact a_step_4
  · exact a_step_5
  · exact a_step_6
  · exact a_step_7
  · exact a_step_8
  · exact a_step_9
  · exact a_step_10
  · exact a_step_11
  · exact a_step_12
  · exact a_step_13

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceTransitions
