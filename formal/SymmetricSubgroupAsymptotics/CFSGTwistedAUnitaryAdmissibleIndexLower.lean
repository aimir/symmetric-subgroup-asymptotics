import SymmetricSubgroupAsymptotics.CFSGTwistedA2HeisenbergModelIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMinimumIndexLower

/-! The Heisenberg lower bound for EVERY classifier-admissible twisted-A
rank. The exceptional rank-two q=2 tag is excluded exactly by the
original classifier guard; higher ranks retain q=2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open PrimitiveSocleRawStructure

theorem twistedA_admissible_field_power_le_proper_index (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (hsmall : r = 2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (H : Subgroup (CFSG.Models.TwistedA r q)) (hH : H ≠ ⊤) : q.order ^ r ≤ H.index := by
  by_cases htwo : r = 2
  · subst r
    have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact twistedA_rankTwo_field_square_le_proper_index q (by have := hsmall rfl; omega) H hH
  · exact twistedA_higher_field_power_le_proper_index r (by omega) q H hH

theorem twistedA_admissible_order_power_le_leastProperIndex (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (hsmall : r = 2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA r q) ell) : q.order ^ r ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  rw [← he]
  exact twistedA_admissible_field_power_le_proper_index r hr q hsmall H hH

theorem twistedA_admissible_rank_mul_log_order_le_log_leastProperIndex
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower) (hsmall : r = 2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA r q) ell) :
    (r : ℝ) * Real.logb 2 q.order ≤ Real.logb 2 ell := by
  have hnat := twistedA_admissible_order_power_le_leastProperIndex r hr q hsmall ell hell
  have hq : 0 < q.order := pow_pos q.prime_isPrime.pos _
  have hreal : (q.order : ℝ) ^ r ≤ (ell : ℝ) := by exact_mod_cast hnat
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (q.order : ℝ) ^ r) hreal
  simpa only [Real.logb_pow] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
