import SymmetricSubgroupAsymptotics.CFSGUnitaryOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryAdmissibleIndexLower
import SymmetricSubgroupAsymptotics.FieldRankIndexOrderNumerics

/-! The actual original unitary model's order is bounded above in terms
of EVERY proper subgroup's index, uniformly in all admissible fields
and ranks. The two inputs are proved matrix covers and Heisenberg index
lower bounds on the same original model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

theorem twistedA_admissible_order_le_proper_index_log_power
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (H : Subgroup (CFSG.Models.TwistedA r q)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.TwistedA r q) ≤ H.index^(4*Nat.log 2 H.index+1) := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact (twistedA_admissible_order_le_matrix_space r hr q hsmall).trans
    (FieldRankIndexOrderNumerics.matrix_power_le_index_log_power q.order r H.index hq hr
      (twistedA_admissible_field_power_le_proper_index r hr q hsmall H hH))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
