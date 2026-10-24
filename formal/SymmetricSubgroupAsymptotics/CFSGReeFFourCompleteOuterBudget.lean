import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGReeFFourPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGFFourOuterBudgetNumerics

/-! The original ReeF4 outer budget follows from the proved field-degree
bound and the same group's proper-index lower bound. Tits is excluded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourCompleteOuterBudget
open PrimitiveSocleRawStructure

theorem reeFFour_sufficient_outer_budget (m : ℕ) (hm : 0 < m)
    [Finite (CFSG.Models.ReeF4 m)] [IsSimpleGroup (CFSG.Models.ReeF4 m)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.ReeF4 m) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.ReeF4 m))) := by
  let q : CFSG.PrimePower :=
    { prime := 2, exponent := 2*m+1, prime_isPrime := by decide, exponent_pos := by omega }
  apply CFSGFFourOuterBudgetNumerics.budget_of_base_lower q ell
  · exact CFSGReeFFourPermutationDegree.order_le_leastProperIndex m hm ell hell
  · change Nat.card (Outer (CFSG.Models.ReeF4 m))≤2*(2*m+1)
    exact (CFSGReeFFourOriginalOuterBound.outer_card_le m hm).trans (by omega)

end SymmetricSubgroupAsymptotics.CFSGReeFFourCompleteOuterBudget
