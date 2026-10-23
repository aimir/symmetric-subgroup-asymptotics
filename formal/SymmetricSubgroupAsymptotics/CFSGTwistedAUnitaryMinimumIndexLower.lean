import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergModelIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Actual original twisted-A least-index lower bounds in every rank at
least three, from the literal Heisenberg action. Rank two is not silently
included in this all-rank reindex adapter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open PrimitiveSocleRawStructure

theorem twistedA_higher_field_power_le_proper_index (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (H : Subgroup (CFSG.Models.TwistedA r q)) (hH : H ≠ ⊤) : q.order ^ r ≤ H.index := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => omega
    | succ r =>
      cases r with
      | zero => omega
      | succ s => exact twistedA_shifted_field_power_le_proper_index q s H hH

theorem twistedA_order_power_le_leastProperIndex (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA r q) ell) : q.order ^ r ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  rw [← he]
  exact twistedA_higher_field_power_le_proper_index r hr q H hH

theorem twistedA_rank_mul_log_order_le_log_leastProperIndex (r : ℕ) (hr : 3 ≤ r)
    (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedA r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA r q) ell) :
    (r : ℝ) * Real.logb 2 q.order ≤ Real.logb 2 ell := by
  have hnat := twistedA_order_power_le_leastProperIndex r hr q ell hell
  have hq : 0 < q.order := pow_pos q.prime_isPrime.pos _
  have hreal : (q.order : ℝ) ^ r ≤ (ell : ℝ) := by exact_mod_cast hnat
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (q.order : ℝ) ^ r) hreal
  simpa only [Real.logb_pow] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
