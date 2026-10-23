import SymmetricSubgroupAsymptotics.CFSGGTwoCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGGTwoIndexSquareSufficientSimpleIndex

/-! The original G2 branch is discharged completely from the remaining
sufficient-simple-index model callback. All other residuals are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterGTwoOuter : CFSG.Index → Prop
  | .G2 _ _ => False
  | i => RemainingSufficientSimpleIndexAfterFFourOuter i

theorem modelBoundsAfterGTwoSquare_of_remaining_after_GTwo_outer
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hi : RemainingSufficientSimpleIndexAfterFFourOuter i)
    (remaining : RemainingSufficientSimpleIndexAfterGTwoOuter i → ModelBoundsAfterGTwoIndexSquare i) :
    ModelBoundsAfterGTwoIndexSquare i := by
  cases i <;> try exact remaining hi
  case G2 q hsmall hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.G2 q) := hsimple
    exact CFSGGTwoCompleteOuterBudget.typeGTwo_sufficient_outer_budget q hsmall

end SymmetricSubgroupAsymptotics.CFSGReduction
