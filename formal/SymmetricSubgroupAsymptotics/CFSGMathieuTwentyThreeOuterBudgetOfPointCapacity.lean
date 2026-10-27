import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeNormalizedFixedPointFibre
import SymmetricSubgroupAsymptotics.PrimePeriodSimpleQuotientIndex
import SymmetricSubgroupAsymptotics.CFSGMathieuPrimeTwentyThreeOuterNumerics

/-! Internal numerical consumer of the exact original point fibre.
Its capacity must be proved before a complete endpoint can use this file;
it is not an additional T1 assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeOuterBudgetOfPointCapacity
open PrimitiveSocleRawStructure CFSG.Models.Presentations.M23
open CFSGMathieuTwentyThreeNormalizedFixedPointFibre

variable [Finite Model] [IsSimpleGroup Model]

theorem proper_index_ge_twentyThree (K : Subgroup Model) (hK : K ≠ ⊤) :
    23 ≤ K.index := by
  have hdiv : 23 ∣ Nat.card Model := by
    have hcard := CFSGMathieuTwentyThreeParityOuterReduction.selectedSylow_spec.1
    rw [←hcard]
    exact (CFSGMathieuTwentyThreeParityOuterReduction.selectedSylow : Subgroup Model).card_subgroup_dvd_card
  exact PrimePeriodSimpleQuotientIndex.prime_le_proper_index 23 (by decide) hdiv K hK

theorem outer_card_le_thirteen_of_point_capacity (hn : ¬IsMulCommutative Model)
    (hcapacity : Nat.card (pointFibre 0) ≤ 20) : Nat.card (Outer Model) ≤ 13 := by
  have hh := three_mul_outer_card_le_twice_pointFibre hn
  omega

theorem sufficient_outer_budget_of_point_capacity (hn : ¬IsMulCommutative Model)
    (ell : ℕ) (hell : LeastProperIndex Model ell)
    (hcapacity : Nat.card (pointFibre 0) ≤ 20) :
    SufficientOuterOrderBudget ell (Nat.card (Outer Model)) := by
  obtain ⟨K,hK,hindex⟩ := hell.1
  have he : 23 ≤ ell := by
    have hi := proper_index_ge_twentyThree K hK
    omega
  exact CFSGMathieuPrimeTwentyThreeOuterNumerics.sufficient_budget_of_le_thirteen ell _ he
    (outer_card_le_thirteen_of_point_capacity hn hcapacity)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeOuterBudgetOfPointCapacity
