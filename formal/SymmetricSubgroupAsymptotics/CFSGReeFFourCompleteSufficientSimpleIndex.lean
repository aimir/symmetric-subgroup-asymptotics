import SymmetricSubgroupAsymptotics.CFSGReeFFourCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGReeFFourIndexSquareSufficientSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGReeGTwoCompleteSufficientSimpleIndex

/-! Both numerical obligations for every original ReeF4 parameter are
proved. The remaining numerical callback excludes this entire family;
the separate Tits model is unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterReeFFourOuter : CFSG.Index → Prop
  | .reeF4 _ _ => False
  | i => RemainingSufficientSimpleIndexAfterReeGTwoOuter i

theorem modelBoundsAfterReeFFourSquare_of_remaining_after_ReeFFour_outer
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hi : RemainingSufficientSimpleIndexAfterReeGTwoOuter i)
    (remaining : RemainingSufficientSimpleIndexAfterReeFFourOuter i →
      ModelBoundsAfterReeFFourIndexSquare i) : ModelBoundsAfterReeFFourIndexSquare i := by
  cases i <;> try exact remaining hi
  case reeF4 m hm hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := hsimple
    exact CFSGReeFFourCompleteOuterBudget.reeFFour_sufficient_outer_budget m (by omega)

end SymmetricSubgroupAsymptotics.CFSGReduction
