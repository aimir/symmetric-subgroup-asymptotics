import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGGTwoPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGFFourOuterBudgetNumerics

/-! The complete numerical outer budget of the original admissible G2
model follows from its actual 2f bound and original q<=ell inequality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCompleteOuterBudget
open PrimitiveSocleRawStructure

theorem typeGTwo_sufficient_outer_budget (q : CFSG.PrimePower) (hsmall : q.order≠2)
    [IsSimpleGroup (CFSG.Models.G2 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.G2 q) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.G2 q))) := by
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hq3 : 3 ≤ Nat.card q.Field := by rw [q.card_field]; omega
  apply CFSGFFourOuterBudgetNumerics.budget_of_base_lower q ell
  · simpa only [q.card_field] using
      CFSGGTwoPermutationDegree.field_card_le_leastProperIndex q.Field hq3 ell hell
  · exact CFSGGTwoD4GeckOriginalOuterBound.typeGTwo_outer_card_le_two_exponent q

end SymmetricSubgroupAsymptotics.CFSGGTwoCompleteOuterBudget
