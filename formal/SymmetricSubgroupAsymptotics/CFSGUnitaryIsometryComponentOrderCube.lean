import SymmetricSubgroupAsymptotics.CFSGUnitaryIsometryOrderUpper
import SymmetricSubgroupAsymptotics.CFSGUnitaryProperIndexOuterUpper
import SymmetricSubgroupAsymptotics.CFSGUnitaryAdmissibleIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.UnitaryIsometryOrderCubeNumerics

/-! The same original unitary component has a stronger uniform order
cube, using actual isometries and the actual outer group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryIsometryComponentOrderCube
open PrimitiveSocleRawStructure CFSGTwistedAUnitaryCoordinates CFSGReduction
open UnitaryIsometryOrderCubeNumerics

theorem twice_exponent_le_order (q : CFSG.PrimePower) : 2*q.exponent ≤ q.order := by
  have hpow : ∀ f : ℕ, 1 ≤ f → 2*f ≤ 2^f := by
    intro f hf
    induction f, hf using Nat.le_induction with
    | base => decide
    | succ f hf ih =>
      have hp : 2 ≤ 2^f := (by norm_num : 2=2^1).le.trans
        (Nat.pow_le_pow_right (by decide) hf)
      rw [pow_succ]
      omega
  exact (hpow q.exponent q.exponent_pos).trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)

theorem raw_outer_le_power (r : ℕ) (_hr : 2 ≤ r) (q : CFSG.PrimePower) :
    2*(r+1)*q.exponent ≤ q.order^(r+1) := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hrq : r+1 ≤ q.order^r :=
    (Nat.succ_le_of_lt r.lt_two_pow_self).trans (Nat.pow_le_pow_left hq r)
  calc
    2*(r+1)*q.exponent = (r+1)*(2*q.exponent) := by ring
    _ ≤ q.order^r*q.order := Nat.mul_le_mul hrq (twice_exponent_le_order q)
    _ = q.order^(r+1) := (pow_succ _ _).symm

theorem component_le_field_power (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hnc : ¬IsMulCommutative (CFSG.Models.TwistedA r q)) :
    Nat.card (CFSG.Models.TwistedA r q) * Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤
      q.order^exponent r := by
  have ho := (twistedA_admissible_raw_outer_order_le r hr q hsmall hnc).trans
    (raw_outer_le_power r hr q)
  calc
    _ ≤ q.order^((r+1)*(r+2)) * q.order^(r+1) :=
      Nat.mul_le_mul (twistedA_admissible_order_le_isometry_power r hr q hsmall) ho
    _ = q.order^exponent r := by
      rw [←pow_add]
      congr 1

theorem component_order_cube (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hnc : ¬IsMulCommutative (CFSG.Models.TwistedA r q)) (hc : Capacity q.order r) :
    (Nat.card (CFSG.Models.TwistedA r q)*Nat.card (Outer (CFSG.Models.TwistedA r q)))^3 ≤
      5^(q.order^r-1) := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have h := Nat.pow_le_pow_left (component_le_field_power r hr q hsmall hnc) 3
  have he : (q.order^exponent r)^3 = q.order^(3*exponent r) := by
    rw [←pow_mul,Nat.mul_comm]
  exact (h.trans_eq he).trans (order_cube q.order r hq hr hc)

theorem order_ge_1024 (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hc : Capacity q.order r) : 1024 ≤ Nat.card (CFSG.Models.TwistedA r q) := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex (CFSG.Models.TwistedA r q)
  have hlo := (root_power_ge q.order r hq hr hc).trans
    (twistedA_admissible_order_power_le_leastProperIndex r hr q hsmall ell hell)
  have hs := twistedA_admissible_leastIndex_square_lt r hr q hsmall ell hell
  have hp := Nat.pow_le_pow_left hlo 2
  norm_num only [Nat.reducePow] at hp
  omega

end SymmetricSubgroupAsymptotics.CFSGUnitaryIsometryComponentOrderCube
