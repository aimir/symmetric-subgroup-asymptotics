import SymmetricSubgroupAsymptotics.CFSGTwistedDOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedDIndexStarLower
import SymmetricSubgroupAsymptotics.CFSGTwistedDOuterBudgetNumerics

/-! The proved original root-star degree lower bound installs the
actual outer estimate in every admissible nonsplit D rank. The exact
characteristic budget uses only q^(r-2), without a cubic lower bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDOuterBudget
open CFSGTwistedDOuterCardinality CFSGTwistedDIndexStarLower
open CFSGTwistedDOuterBudgetNumerics PrimitiveSocleRawStructure

theorem original_outer_budget (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedD (s + 4) q)) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedD (s + 4) q) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.TwistedD (s + 4) q))) := by
  have hlow := original_field_power_le_leastProperIndex s q ell hell
  have hq := CFSGTwistedAQuadraticTrace.order_two_le q
  have hsq : q.order ^ 2 ≤ ell :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ q.order) (by omega : 2 ≤ s + 2)).trans hlow
  exact budget_of_square_lower q ell _ hsq (original_outer_card_le_eight_exponent s q hn)
    (original_binary_outer_card_le_four_exponent s q hn)

end SymmetricSubgroupAsymptotics.CFSGTwistedDOuterBudget

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeTwistedD_sufficientOuterBudget (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedD r q)) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedD r q) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.TwistedD r q))) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
  exact CFSGTwistedDOuterBudget.original_outer_budget s q hn ell hell

end SymmetricSubgroupAsymptotics.CFSGReduction
