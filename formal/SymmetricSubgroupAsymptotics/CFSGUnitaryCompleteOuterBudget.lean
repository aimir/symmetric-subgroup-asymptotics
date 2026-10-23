import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySemilinearFactorization
import SymmetricSubgroupAsymptotics.CFSGUnitarySemilinearAutomorphismCardinality
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoOuterBudget

/-! Complete outer budget on the ORIGINAL unitary models. Higher ranks
use the constructed semilinear point factorization and the projective
image count. Rank two reuses its checked original-model reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open PrimitiveSocleRawStructure

theorem twistedA_higher_outer_order_le (q : CFSG.PrimePower) (s : ℕ)
    [IsSimpleGroup (CFSG.Models.TwistedA (s+3) q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA (s+3) q)) :
    Nat.card (Outer (CFSG.Models.TwistedA (s+3) q)) ≤ 2 * q.exponent * (s+4) := by
  exact unitary_outer_card_le_of_aut_naturalFixed_bound q s hn
    (unitary_card_aut_le_of_field_linear_factor q s (unitary_exists_field_linear_factor q s))

theorem twistedA_admissible_sufficient_outer_budget (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (hsmall : r=2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA r q))
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.TwistedA r q) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.TwistedA r q))) := by
  by_cases htwo : r=2
  · subst r
    have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact twistedA_rankTwo_sufficient_outer_budget q (by have := hsmall rfl; omega) ell hell
  · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3, by omega⟩
    apply twistedA_outer_budget_of_raw (s+3) (by omega) q hsmall ell _ hell
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using twistedA_higher_outer_order_le q s hn

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
