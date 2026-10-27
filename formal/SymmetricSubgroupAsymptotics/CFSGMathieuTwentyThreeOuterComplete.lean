import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePackedFullPointFibreCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeOuterBudgetOfPointCapacity

/-! The literal point-fibre capacity is supplied internally, not as a
new input. This closes the remaining M23 outer numerical budget. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeOuterComplete
open PrimitiveSocleRawStructure CFSG.Models.Presentations.M23

variable [Finite Model] [IsSimpleGroup Model]

theorem outer_card_le_thirteen (hn : ¬IsMulCommutative Model) :
    Nat.card (Outer Model) ≤ 13 :=
  CFSGMathieuTwentyThreeOuterBudgetOfPointCapacity.outer_card_le_thirteen_of_point_capacity hn
    CFSGMathieuTwentyThreePackedFullPointFibreCapacity.pointFibre_card_le_twenty

theorem outer_card_le_four (hn : ¬IsMulCommutative Model) :
    Nat.card (Outer Model) ≤ 4 := by
  have hc : Nat.card (CFSGMathieuTwentyThreeNormalizedFixedPointFibre.pointFibre 0) ≤ 7 :=
    CFSGMathieuTwentyThreePackedFullPointFibreCapacity.pointFibre_card_le_count
  have hh := CFSGMathieuTwentyThreeNormalizedFixedPointFibre.three_mul_outer_card_le_twice_pointFibre hn
  omega

theorem sufficient_outer_budget (hn : ¬IsMulCommutative Model)
    (ell : ℕ) (hell : LeastProperIndex Model ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer Model)) :=
  CFSGMathieuTwentyThreeOuterBudgetOfPointCapacity.sufficient_outer_budget_of_point_capacity hn ell hell
    CFSGMathieuTwentyThreePackedFullPointFibreCapacity.pointFibre_card_le_twenty

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeOuterComplete
