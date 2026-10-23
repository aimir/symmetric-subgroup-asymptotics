import SymmetricSubgroupAsymptotics.CFSGReeGTwoCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexSquareSufficientSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoCompleteSufficientSimpleIndex

/-! Both numerical obligations of the literal ReeG2 model are proved.
The remaining simple-index callback therefore excludes that branch. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterReeGTwoOuter : CFSG.Index → Prop
  | .reeG2 _ _ => False
  | i => RemainingSufficientSimpleIndexAfterGTwoOuter i

theorem modelBoundsAfterReeGTwoSquare_of_remaining_after_ReeGTwo_outer
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hi : RemainingSufficientSimpleIndexAfterGTwoOuter i)
    (remaining : RemainingSufficientSimpleIndexAfterReeGTwoOuter i →
      ModelBoundsAfterReeGTwoIndexSquare i) : ModelBoundsAfterReeGTwoIndexSquare i := by
  cases i <;> try exact remaining hi
  case reeG2 m hm hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := hsimple
    exact CFSGReeGTwoCompleteOuterBudget.reeGTwo_sufficient_outer_budget m hm

end SymmetricSubgroupAsymptotics.CFSGReduction
