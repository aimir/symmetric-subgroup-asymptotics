import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourCompleteWhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourOuterBudgetOfSwapCapacity

/-! The complete literal swap-fibre certificate supplies its own numerical
capacity. No capacity premise is added to this model consumer or T1.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourOuterComplete
open PrimitiveSocleRawStructure CFSG.Models.Presentations.M24
open CFSGMathieuTwentyFourSwapFibreOuterReduction

variable [Finite Model] [IsSimpleGroup Model]

theorem swapFibre_card_le_one : Nat.card SwapFibre ≤ 1 := by
  simpa only [CFSGMathieuTwentyFourCompleteWhitelistCapacity.computedTotal] using
    CFSGMathieuTwentyFourCompleteWhitelistCapacity.swap_card_le_total

theorem outer_card_le_two : Nat.card (Outer Model) ≤ 2 := by
  simpa only [CFSGMathieuTwentyFourCompleteWhitelistCapacity.computedTotal, Nat.mul_one] using
    CFSGMathieuTwentyFourCompleteWhitelistCapacity.outer_card_le_twice_total

theorem swapFibre_card_le_six : Nat.card SwapFibre ≤ 6 :=
  CFSGMathieuTwentyFourCompleteWhitelistCapacity.swap_card_le_total.trans
    CFSGMathieuTwentyFourCompleteWhitelistCapacity.computedTotal_le_six

theorem outer_card_le_twelve : Nat.card (Outer Model) ≤ 12 :=
  CFSGMathieuTwentyFourOuterBudgetOfSwapCapacity.outer_card_le_twelve_of_swap_capacity
    swapFibre_card_le_six

theorem sufficient_outer_budget (ell : ℕ) (hell : LeastProperIndex Model ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer Model)) :=
  CFSGMathieuTwentyFourOuterBudgetOfSwapCapacity.sufficient_outer_budget_of_swap_capacity
    ell hell swapFibre_card_le_six

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourOuterComplete
