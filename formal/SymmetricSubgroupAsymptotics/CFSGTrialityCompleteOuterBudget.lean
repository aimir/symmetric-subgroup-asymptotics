import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGExceptionalFieldOuterNumerics

/-! Complete outer-order budget for the ORIGINAL triality model. Its
proved 3f outer bound and q^3 <= 2 ell degree estimate discharge every
logarithmic and small-index clause without an automorphism hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityCompleteOuterBudget
open CFSGTrialityGeckOriginalOuterBound CFSGTrialityGeckPermutationDegree
open CFSGExceptionalFieldOuterNumerics PrimitiveSocleRawStructure

theorem typeTriality_sufficient_outer_budget (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TrialityD4 q) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.TrialityD4 q))) :=
  three_field_budget_of_half_cube_lower q ell _ (order_cube_le_twice_leastProperIndex q ell hell)
    (original_outer_card_le_three_exponent q)

end SymmetricSubgroupAsymptotics.CFSGTrialityCompleteOuterBudget
