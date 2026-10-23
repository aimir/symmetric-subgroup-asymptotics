import SymmetricSubgroupAsymptotics.CFSGTwistedE6OriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGExceptionalFieldOuterNumerics

/-! Complete outer-order budget for ORIGINAL twisted E6. The actual
inner-aligned torus index is at most three, and one literal quadratic
field-automorphism factor has order 2f. The proved q^2 index lower bound
discharges all logarithmic and small-degree clauses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6CompleteOuterBudget
open CFSGTwistedE6OriginalOuterBound CFSGTwistedE6GeckPermutationDegree
open CFSGExceptionalFieldOuterNumerics CFSGFiniteFieldAutomorphisms PrimitiveSocleRawStructure
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

theorem typeTwistedE6_outer_card_le_six_exponent (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Nat.card (Outer (CFSG.Models.TwistedE6 q)) ≤ 6*q.exponent := by
  have hc : Nat.card (RingAut (q.Extension 2)) = 2*q.exponent :=
    card_galoisField_ringAut q.prime (2*q.exponent) (by have := q.exponent_pos; omega)
  have hh := typeTwistedE6_outer_card_le q
  rw [hc] at hh
  simpa only [← Nat.mul_assoc, show (3 : ℕ)*2=6 by decide] using hh

theorem typeTwistedE6_sufficient_outer_budget (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedE6 q) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.TwistedE6 q))) :=
  six_field_budget_of_square_lower q ell _ (order_square_le_leastProperIndex q ell hell)
    (typeTwistedE6_outer_card_le_six_exponent q)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6CompleteOuterBudget
