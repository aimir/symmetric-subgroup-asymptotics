import SymmetricSubgroupAsymptotics.CFSGFFourCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGTrialityCompleteSufficientSimpleIndex

/-! The ORIGINAL F4 branch now leaves the sufficient-simple-index
callback completely. Triality and twisted E6 remain discharged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterFFourOuter : CFSG.Index → Prop
  | .F4 _ => False
  | i => RemainingSufficientSimpleIndexAfterTrialityOuter i

theorem modelBoundsAfterFFourTwistedE6Squares_of_remaining_after_fFour_outer
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hi : RemainingSufficientSimpleIndexAfterTrialityOuter i)
    (remaining : RemainingSufficientSimpleIndexAfterFFourOuter i →
      ModelBoundsAfterFFourTwistedE6IndexSquares i) :
    ModelBoundsAfterFFourTwistedE6IndexSquares i := by
  cases i <;> try exact remaining hi
  case F4 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.F4 q) := hsimple
    exact CFSGFFourCompleteOuterBudget.typeFFour_sufficient_outer_budget q

end SymmetricSubgroupAsymptotics.CFSGReduction
