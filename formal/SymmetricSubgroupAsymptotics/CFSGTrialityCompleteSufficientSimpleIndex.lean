import SymmetricSubgroupAsymptotics.CFSGTrialityCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGTwistedE6CompleteSufficientSimpleIndex

/-! ORIGINAL triality now leaves the sufficient-simple-index residual
completely, preserving the completed original twisted E6 branch. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterTrialityOuter : CFSG.Index → Prop
  | .trialityD4 _ => False
  | i => RemainingSufficientSimpleIndexAfterTwistedE6Outer i

theorem modelBoundsAfterFFourTwistedE6Squares_of_remaining_after_triality_outer
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hi : RemainingSufficientSimpleIndexAfterTwistedE6Outer i)
    (remaining : RemainingSufficientSimpleIndexAfterTrialityOuter i →
      ModelBoundsAfterFFourTwistedE6IndexSquares i) :
    ModelBoundsAfterFFourTwistedE6IndexSquares i := by
  cases i <;> try exact remaining hi
  case trialityD4 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := hsimple
    exact CFSGTrialityCompleteOuterBudget.typeTriality_sufficient_outer_budget q

end SymmetricSubgroupAsymptotics.CFSGReduction
