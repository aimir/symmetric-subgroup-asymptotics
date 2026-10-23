import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGFFourE6PermutationDegree
import SymmetricSubgroupAsymptotics.CFSGFFourOuterBudgetNumerics

/-! Complete outer-order budget on the ORIGINAL F4 model. The actual
signed-root label index is at most two, the scalar index is one, and
the common field contributes f. The proved q <= ell lower bound supplies
every logarithmic and small-index clause. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourCompleteOuterBudget
open PrimitiveSocleRawStructure
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

theorem typeFFour_sufficient_outer_budget (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.F4 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.F4 q) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.F4 q))) := by
  apply CFSGFFourOuterBudgetNumerics.budget_of_base_lower q ell
  · simpa only [q.card_field] using
      CFSGFFourE6PermutationDegree.field_card_le_leastProperIndex q.Field q.prime ell hell
  · exact CFSGFFourE6OriginalOuterBound.typeFFour_outer_card_le_two_exponent q

end SymmetricSubgroupAsymptotics.CFSGFFourCompleteOuterBudget
