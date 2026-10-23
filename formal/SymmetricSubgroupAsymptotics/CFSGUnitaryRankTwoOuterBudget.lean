import SymmetricSubgroupAsymptotics.CFSGTwistedA2OuterOrder
import SymmetricSubgroupAsymptotics.CFSGUnitaryOuterBudgetNumerics

/-! The proved rank-two unitary outer estimate supplies the actual
sufficient outer budget on every classifier-admissible rank-two tag. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open PrimitiveSocleRawStructure

theorem twistedA_rankTwo_sufficient_outer_budget (q : CFSG.PrimePower)
    (hq : 3 ≤ q.order) [IsSimpleGroup (CFSG.Models.TwistedA 2 q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.TwistedA 2 q) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.TwistedA 2 q))) := by
  apply twistedA_outer_budget_of_raw 2 (by omega) q (by omega) ell _ hell
  simpa using twistedA_rankTwo_outer_order_le_six_exponent q hq

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
