import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGFFourOuterBudgetNumerics

/-! The original ReeG2 outer budget follows from its proved 2f bound and
the defining-field lower bound for every proper permutation degree. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoCompleteOuterBudget
open PrimitiveSocleRawStructure

theorem reeGTwo_sufficient_outer_budget (m : ℕ) (hm : 1 ≤ m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.ReeG2 m) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.ReeG2 m))) := by
  let q : CFSG.PrimePower :=
    { prime := 3, exponent := 2*m+1, prime_isPrime := by decide, exponent_pos := by omega }
  apply CFSGFFourOuterBudgetNumerics.budget_of_base_lower q ell
  · exact CFSGReeGTwoPermutationDegree.field_card_le_leastProperIndex m hm ell hell
  · exact CFSGReeGTwoOriginalOuterBound.outer_card_le m hm

end SymmetricSubgroupAsymptotics.CFSGReeGTwoCompleteOuterBudget
