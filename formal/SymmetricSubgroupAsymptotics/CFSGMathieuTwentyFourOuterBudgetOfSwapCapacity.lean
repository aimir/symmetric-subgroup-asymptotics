import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSwapFibreOuterReduction
import SymmetricSubgroupAsymptotics.PrimePeriodSimpleQuotientIndex
import SymmetricSubgroupAsymptotics.CFSGMathieuPrimeTwentyThreeOuterNumerics

/-! Internal consumer of a proved bound on the literal original swap fibre.
This conditional lemma does not add a capacity premise to T1. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourOuterBudgetOfSwapCapacity
open PrimitiveSocleRawStructure CFSG.Models.Presentations.M24
open CFSGMathieuTwentyFourSwapFibreOuterReduction

variable [Finite Model] [IsSimpleGroup Model]

theorem proper_index_ge_twentyThree (K : Subgroup Model) (hK : K ≠ ⊤) :
    23 ≤ K.index := by
  have hdiv : 23 ∣ Nat.card Model := by
    have hcard := CFSGMathieuTwentyFourParityOuterReduction.selectedSylow_spec.1
    rw [←hcard]
    exact (CFSGMathieuTwentyFourParityOuterReduction.selectedSylow : Subgroup Model).card_subgroup_dvd_card
  exact PrimePeriodSimpleQuotientIndex.prime_le_proper_index 23 (by decide) hdiv K hK

theorem outer_card_le_twelve_of_swap_capacity
    (hcapacity : Nat.card SwapFibre ≤ 6) : Nat.card (Outer Model) ≤ 12 := by
  have hh := outer_card_le_twice_swap
  omega

theorem sufficient_outer_budget_of_swap_capacity
    (ell : ℕ) (hell : LeastProperIndex Model ell)
    (hcapacity : Nat.card SwapFibre ≤ 6) :
    SufficientOuterOrderBudget ell (Nat.card (Outer Model)) := by
  obtain ⟨K,hK,hindex⟩ := hell.1
  have he : 23 ≤ ell := by
    have hi := proper_index_ge_twentyThree K hK
    omega
  exact CFSGMathieuPrimeTwentyThreeOuterNumerics.sufficient_budget_of_le_thirteen ell _ he
    ((outer_card_le_twelve_of_swap_capacity hcapacity).trans (by decide))

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourOuterBudgetOfSwapCapacity
