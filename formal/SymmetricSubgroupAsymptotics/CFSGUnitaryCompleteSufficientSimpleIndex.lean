import SymmetricSubgroupAsymptotics.CFSGUnitaryCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGTwistedDCompleteSufficientSimpleIndex

/-! All admissible original unitary tags now leave the sufficient-index
residual, retaining the completed original nonsplit-D branch. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingSufficientSimpleIndexAfterUnitaryOuter : CFSG.Index → Prop
  | .twistedA _ _ _ _ => False
  | i => RemainingSufficientSimpleIndexAfterTwistedDOuter i

theorem modelBoundsAfterTwistedDSquare_of_remaining_after_unitary_outer
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬ IsMulCommutative i.Model)
    (hi : RemainingSufficientSimpleIndexAfterTwistedDOuter i)
    (remaining : RemainingSufficientSimpleIndexAfterUnitaryOuter i → ModelBoundsAfterTwistedDSquare i) :
    ModelBoundsAfterTwistedDSquare i := by
  cases i <;> try exact remaining hi
  case twistedA r q hr hsmall hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := hsimple
    intro ell hell
    exact CFSGTwistedAUnitaryCoordinates.twistedA_admissible_sufficient_outer_budget
      r hr q hsmall hn ell hell

end SymmetricSubgroupAsymptotics.CFSGReduction
