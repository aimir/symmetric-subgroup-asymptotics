import SymmetricSubgroupAsymptotics.SemisimpleNormalChart
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The natural primitive semisimple outer-log profile -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The primitive-socle data in its natural literature form.  The structure
retains the published outer-order estimate; exact one-factor socle facts are
kept in a separate wrapper at the classification boundary. -/
structure PrimitiveSemisimpleOuterLogProfile
    (L : Type) [Group L] (r : ℕ) where
  E : Subgroup L
  [E_normal : E.Normal]
  chart : SemisimpleNormalChart E
  factorCount : ℕ
  factorCount_pos : 0 < factorCount
  leastIndex : ℕ
  leastIndex_five_le : 5 ≤ leastIndex
  outerOrder : ℕ
  outerOrder_pos : 0 < outerOrder
  quotientAction :
    (L ⧸ E) →* Equiv.Perm (Fin (factorCount * outerOrder))
  quotientAction_injective : Function.Injective quotientAction
  primitive_index_lower : leastIndex ^ factorCount ≤ r
  outerOrder_log_bound :
    (outerOrder : ℝ) ≤ 3 * Real.logb 2 leastIndex

attribute [instance] PrimitiveSemisimpleOuterLogProfile.E_normal

end SymmetricSubgroupAsymptotics

end
