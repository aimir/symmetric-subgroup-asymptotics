import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedFullCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOuterBudgetOfFixedCapacity

/-! The finite fixed-generator capacity is proved internally. This module
therefore discharges the actual M22 outer budget without a new premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOuterComplete
open PrimitiveSocleRawStructure

theorem outer_card_le_eight [IsSimpleGroup CFSG.Models.Mathieu22] :
    Nat.card (Outer CFSG.Models.Mathieu22) ≤ 8 :=
  CFSGMathieuTwentyTwoOuterBudgetOfFixedCapacity.outer_card_le_eight_of_fixed_capacity
    CFSGMathieuTwentyTwoPackedFullCapacity.fixedAutomorphisms_card_le_fortyFour

theorem sufficient_outer_budget [IsSimpleGroup CFSG.Models.Mathieu22]
    (ell : ℕ) (hell : LeastProperIndex CFSG.Models.Mathieu22 ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Mathieu22)) :=
  CFSGMathieuTwentyTwoOuterBudgetOfFixedCapacity.sufficient_outer_budget_of_fixed_capacity
    ell hell CFSGMathieuTwentyTwoPackedFullCapacity.fixedAutomorphisms_card_le_fortyFour

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOuterComplete
