import SymmetricSubgroupAsymptotics.CFSGTwistedE6CompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGFFourTwistedE6IndexSquaresSufficientSimpleIndex

/-! Original twisted E6 now leaves the simple-index residual completely.
Its actual index square and outer budget are proved, including all fields.
The F4/triality outer leaves and every other residual tag remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterTwistedE6Outer : CFSG.Index → Prop
  | .twistedE6 _ => False
  | i => RemainingSufficientSimpleIndexAfterUnitaryOuter i

theorem modelBoundsAfterFFourTwistedE6Squares_of_remaining_after_twistedE6_outer
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hi : RemainingSufficientSimpleIndexAfterUnitaryOuter i)
    (remaining : RemainingSufficientSimpleIndexAfterTwistedE6Outer i →
      ModelBoundsAfterFFourTwistedE6IndexSquares i) :
    ModelBoundsAfterFFourTwistedE6IndexSquares i := by
  cases i <;> try exact remaining hi
  case twistedE6 q hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := hsimple
    exact CFSGTwistedE6CompleteOuterBudget.typeTwistedE6_sufficient_outer_budget q

end SymmetricSubgroupAsymptotics.CFSGReduction
