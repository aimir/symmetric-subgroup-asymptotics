import SymmetricSubgroupAsymptotics.External.CFSG.Parameters
import Mathlib.Algebra.IsPrimePow
import Lean.Elab.Tactic.Omega

/-! Small field-order arithmetic follows from the literal prime-power
parameters; it requires no catalogue or classification hypothesis. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGPrimePowerSmallOrders

theorem order_isPrimePow (q : CFSG.PrimePower) : IsPrimePow q.order :=
  (isPrimePow_nat_iff q.order).mpr
    ⟨q.prime,q.exponent,q.prime_isPrime,q.exponent_pos,rfl⟩

theorem order_ne_six (q : CFSG.PrimePower) : q.order≠6 := by
  have h : ¬IsPrimePow (6:ℕ) := by decide
  intro he
  exact h (he ▸ order_isPrimePow q)

theorem order_le_seven_cases (q : CFSG.PrimePower) (hq : q.order≤7) :
    q.order=2 ∨ q.order=3 ∨ q.order=4 ∨ q.order=5 ∨ q.order=7 := by
  have hlo : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hn := order_ne_six q
  omega

end SymmetricSubgroupAsymptotics.CFSGPrimePowerSmallOrders
