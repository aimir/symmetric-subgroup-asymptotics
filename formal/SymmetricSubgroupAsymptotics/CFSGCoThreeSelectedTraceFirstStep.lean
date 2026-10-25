import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceData
import Mathlib.Tactic.FinCases

/-! Exactly the first of fourteen already selected Co3 word applications.
Each of its two actual 22-dimensional matrix-vector transitions is a
kernel-checked coordinate statement. This bounded pilot precedes any
expansion to the other fixed transitions. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceFirstStep
open CFSGCoThreeSelectedTraceData

theorem b_first : b *ᵥ vectors 0 = afterB 0 := by
  funext j
  fin_cases j <;> decide +kernel

theorem a_first : a *ᵥ afterB 0 = vectors 1 := by
  funext j
  fin_cases j <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceFirstStep
