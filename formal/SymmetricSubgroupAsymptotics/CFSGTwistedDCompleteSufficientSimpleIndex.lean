import SymmetricSubgroupAsymptotics.CFSGTwistedDOuterBudget
import SymmetricSubgroupAsymptotics.CFSGTwistedDSquareSufficientSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoSufficientSimpleIndex

/-! Every admissible original nonsplit D model now satisfies both the
proved index square and the complete outer budget. Its tag leaves the
sufficient-simple-index residual. Other tags and their exact requested
data are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterTwistedDOuter : CFSG.Index → Prop
  | .twistedD _ _ _ => False
  | i => RemainingSufficientSimpleIndexAfterUnitaryRankTwo i

theorem modelBoundsAfterTwistedDSquare_of_remaining_after_twistedD_outer
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬ IsMulCommutative i.Model)
    (hi : RemainingSufficientSimpleIndexAfterUnitaryRankTwo i)
    (remaining : RemainingSufficientSimpleIndexAfterTwistedDOuter i → ModelBoundsAfterTwistedDSquare i) :
    ModelBoundsAfterTwistedDSquare i := by
  cases i <;> try exact remaining hi
  case twistedD r q hr hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := hsimple
    intro ell hell
    exact typeTwistedD_sufficientOuterBudget r hr q hn ell hell

end SymmetricSubgroupAsymptotics.CFSGReduction
