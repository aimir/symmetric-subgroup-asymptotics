import SymmetricSubgroupAsymptotics.CFSGUnitaryTenHeadScaledClassPacket
import SymmetricSubgroupAsymptotics.CFSGUnitaryHigherCoupledScaledClassPacket
import SymmetricSubgroupAsymptotics.CFSGUnitaryLowRankScaledTail
import SymmetricSubgroupAsymptotics.CFSGPrimePowerSmallOrders

/-! The complete admissible original unitary scaled class packet.
The infinite ranges and the ten bounded parameters exhaust all ranks
and field orders; all branches retain the same projective model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryCompleteScaledClassPacket
open PrimitiveSocleRawStructure UnitaryTenHeadScaledFrameNumerics

theorem scaled_class_cube_le_proper_index (r : ℕ) (hr : 2≤r)
    (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] [Finite (CFSG.Models.TwistedA r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedA r q))
    (H : Subgroup (CFSG.Models.TwistedA r q)) (hH : H≠⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.TwistedA r q))*
      Nat.card (Outer (CFSG.Models.TwistedA r q)))^3 ≤ 3^H.index := by
  by_cases hlow : (r=2 ∧ 11≤q.order) ∨ (r=3 ∧ 5≤q.order)
  · exact CFSGUnitaryLowRankScaledTail.scaled_class_cube_le_proper_index r q hlow hn H hH
  by_cases hhigh : 4≤r ∧ (r=4 → 3≤q.order)
  · exact CFSGUnitaryHigherCoupledScaledClassPacket.scaled_class_cube_le_proper_index
      r hhigh.1 q hhigh.2 hn H hH
  have hq : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have h10 : q.order≠10 := by
    have hn10 : ¬IsPrimePow (10:ℕ) := by decide +kernel
    intro he
    exact hn10 (he ▸ CFSGPrimePowerSmallOrders.order_isPrimePow q)
  obtain ⟨j,hj⟩ := parameter_of_not_tail r q.order hr hq hsmall
    (CFSGPrimePowerSmallOrders.order_ne_six q) h10 hlow hhigh
  have hrank : (parameters j).1=r := congrArg Prod.fst hj
  have horder : q.order=(parameters j).2 := (congrArg Prod.snd hj).symm
  subst r
  exact CFSGUnitaryTenHeadScaledClassPacket.scaled_class_cube_le_proper_index j q horder hn H hH

end SymmetricSubgroupAsymptotics.CFSGUnitaryCompleteScaledClassPacket
