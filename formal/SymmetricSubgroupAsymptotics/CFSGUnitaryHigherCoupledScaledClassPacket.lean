import SymmetricSubgroupAsymptotics.UnitaryCoupledScaledOrderEnvelope
import SymmetricSubgroupAsymptotics.CFSGUnitaryHigherCoupledIndex
import SymmetricSubgroupAsymptotics.CFSGUnitaryIsometryOrderUpper
import SymmetricSubgroupAsymptotics.CFSGUnitaryProperIndexOuterUpper

/-! The literal higher unitary radical and its SAME normalizer stabilizer
give a coupled index. Together with the proved isometry and outer-order
bounds this pays the scaled class packet without a class census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryHigherCoupledScaledClassPacket
open PrimitiveSocleRawStructure CFSGTwistedAUnitaryCoordinates

theorem scaled_class_cube_le_proper_index
    (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower) (hhead : r=4 → 3 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] [Finite (CFSG.Models.TwistedA r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedA r q))
    (H : Subgroup (CFSG.Models.TwistedA r q)) (hH : H ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.TwistedA r q))*
      Nat.card (Outer (CFSG.Models.TwistedA r q)))^3 ≤ 3^H.index := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hsmall : r=2 → q.order≠2 := by omega
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hrpow : 2*(r+1) ≤ q.order^(r+1) := by
    have he : 2*(r+1) ≤ 2^(r+1) := by
      have hh : r+1 ≤ 2^r := Nat.succ_le_of_lt r.lt_two_pow_self
      exact (Nat.mul_le_mul_left 2 hh).trans_eq (by rw [pow_succ]; ring)
    exact he.trans (Nat.pow_le_pow_left hq _)
  have ho : Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ q.order^(r+2) := by
    calc
      _ ≤ 2*(r+1)*q.exponent :=
        twistedA_admissible_raw_outer_order_le r (by omega) q hsmall hn
      _ ≤ q.order^(r+1)*q.order := Nat.mul_le_mul hrpow hf
      _ = q.order^(r+2) := (pow_succ q.order (r+1)).symm
  have hc : Nat.card (ConjClasses (CFSG.Models.TwistedA r q)) ≤
      q.order^((r+1)*(r+2)) :=
    (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
      (twistedA_admissible_order_le_isometry_power r (by omega) q hsmall)
  have hcomponent : Nat.card (ConjClasses (CFSG.Models.TwistedA r q))*
      Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ q.order^((r+2)^2) := by
    exact (Nat.mul_le_mul hc ho).trans_eq (by
      rw [←pow_add]
      exact congrArg (fun n : ℕ => q.order^n) (by ring))
  have hi : 2*(q.order^2-1)*q.order^(2*r-5) ≤ H.index :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ q.prime_isPrime.two_le)).trans
      (twistedA_higher_coupled_proper_index r hr q H hH)
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hcomponent 3)).trans
    (UnitaryCoupledScaledOrderEnvelope.scaled_order_cube_le q.order r hq hr hhead)).trans
      (Nat.pow_le_pow_right (by decide) hi)

end SymmetricSubgroupAsymptotics.CFSGUnitaryHigherCoupledScaledClassPacket
