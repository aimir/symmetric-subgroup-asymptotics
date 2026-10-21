import SymmetricSubgroupAsymptotics.CFSGTypeAIndexReindex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The actual higher-rank type-A least-index lower bound. It follows
from the original abelian point-root action, not a minimum-index census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAMinimumIndexLower
open PrimitiveSocleRawStructure

theorem order_power_le_leastProperIndex (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.A r q) ell) : q.order^r≤ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  have hh := CFSGTypeAIndexReindex.field_power_le_proper_index
    (F:=q.Field) r hr H hH
  simpa only [q.card_field] using hh

theorem rank_mul_log_order_le_log_leastProperIndex (r : ℕ) (hr : 2≤r)
    (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.A r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.A r q) ell) :
    (r : ℝ)*Real.logb 2 q.order≤Real.logb 2 ell := by
  have hnat := order_power_le_leastProperIndex r hr q ell hell
  have hq : 0<q.order := pow_pos q.prime_isPrime.pos _
  have hreal : (q.order : ℝ)^r≤(ell : ℝ) := by exact_mod_cast hnat
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by positivity : (0 : ℝ)<(q.order : ℝ)^r) hreal
  simpa only [Real.logb_pow] using hh

end SymmetricSubgroupAsymptotics.CFSGTypeAMinimumIndexLower
