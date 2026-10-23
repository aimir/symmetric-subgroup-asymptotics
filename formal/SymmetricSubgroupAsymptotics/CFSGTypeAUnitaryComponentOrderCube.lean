import SymmetricSubgroupAsymptotics.QuadraticRankOrderCubeNumerics
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTypeALeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTypeAMinimumIndexLower
import SymmetricSubgroupAsymptotics.CFSGUnitaryProperIndexOuterUpper
import SymmetricSubgroupAsymptotics.CFSGUnitaryAdmissibleIndexSquare

/-! Concrete original A/unitary ORDER cubes at the proved q^r proper
index. Every estimate is bound to the native model and its actual outer
group. The capacity conditions are explicit field/rank inequalities,
not class-count or recognition callbacks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAUnitaryComponentOrderCube
open PrimitiveSocleRawStructure CFSGReduction CFSGTwistedAUnitaryCoordinates
open QuadraticRankOrderCubeNumerics

private theorem raw_outer_le_field_power (q r f : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r) (hf : f ≤ q) :
    2 * (r + 1) * f ≤ q ^ (2 * r) := by
  have hrq : r + 1 ≤ q ^ r :=
    (Nat.succ_le_of_lt r.lt_two_pow_self).trans (Nat.pow_le_pow_left hq r)
  have h2q : 2 * q ≤ q ^ r := by
    calc
      2 * q ≤ q * q := Nat.mul_le_mul_right q hq
      _ = q ^ 2 := (pow_two q).symm
      _ ≤ q ^ r := Nat.pow_le_pow_right (by omega) hr
  calc
    2 * (r + 1) * f ≤ 2 * q ^ r * q := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hrq) hf
    _ = q ^ r * (2 * q) := by ring
    _ ≤ q ^ r * q ^ r := Nat.mul_le_mul_left _ h2q
    _ = q ^ (2 * r) := by rw [←pow_add]; congr 1; omega

private theorem field_two_le (q : CFSG.PrimePower) : 2 ≤ q.order :=
  q.prime_isPrime.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)

private theorem exponent_le_field (q : CFSG.PrimePower) : q.exponent ≤ q.order :=
  q.exponent.lt_two_pow_self.le.trans (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)

theorem typeA_component_le_field_power (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)] :
    Nat.card (CFSG.Models.A r q) * Nat.card (Outer (CFSG.Models.A r q)) ≤
      q.order ^ typeAExponent r := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have ho : Nat.card (Outer (CFSG.Models.A r q)) ≤ 2 * (r + 1) * q.exponent := by
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
      CFSGTypeAOuterCardinality.outer_card_le (F := q.Field) q.prime (by omega : 3 ≤ r + 1)
  calc
    _ ≤ q.order ^ ((r + 1) ^ 2) * q.order ^ (2 * r) := Nat.mul_le_mul
      (typeA_order_le_matrix_power r q)
      (ho.trans (raw_outer_le_field_power q.order r q.exponent (field_two_le q) hr (exponent_le_field q)))
    _ = q.order ^ typeAExponent r := by rw [←pow_add]; rfl

theorem unitary_component_le_field_power (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r = 2 → q.order ≠ 2) [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hnc : ¬IsMulCommutative (CFSG.Models.TwistedA r q)) :
    Nat.card (CFSG.Models.TwistedA r q) * Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤
      q.order ^ unitaryExponent r := by
  have ho := twistedA_admissible_raw_outer_order_le r hr q hsmall hnc
  calc
    _ ≤ q.order ^ (2 * (r + 1) ^ 2) * q.order ^ (2 * r) := Nat.mul_le_mul
      (twistedA_admissible_order_le_matrix_space r hr q hsmall)
      (ho.trans (raw_outer_le_field_power q.order r q.exponent (field_two_le q) hr (exponent_le_field q)))
    _ = q.order ^ unitaryExponent r := by rw [←pow_add]; rfl

theorem typeA_component_order_cube (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)]
    (hcapacity : 7 ≤ q.order ∨ (4 ≤ q.order ∧ 3 ≤ r) ∨ (3 ≤ q.order ∧ 4 ≤ r) ∨ 7 ≤ r) :
    (Nat.card (CFSG.Models.A r q) * Nat.card (Outer (CFSG.Models.A r q))) ^ 3 ≤
      5 ^ (q.order ^ r - 1) := by
  have h := Nat.pow_le_pow_left (typeA_component_le_field_power r hr q) 3
  have he : (q.order ^ typeAExponent r) ^ 3 = q.order ^ (3 * typeAExponent r) := by
    rw [←pow_mul, Nat.mul_comm]
  exact (h.trans_eq he).trans (typeA_order_cube q.order r (field_two_le q) hr hcapacity)

theorem unitary_component_order_cube (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r = 2 → q.order ≠ 2) [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hnc : ¬IsMulCommutative (CFSG.Models.TwistedA r q))
    (hcapacity : 10 ≤ q.order ∨ (5 ≤ q.order ∧ 3 ≤ r) ∨ (4 ≤ q.order ∧ 4 ≤ r) ∨
      (3 ≤ q.order ∧ 5 ≤ r) ∨ 8 ≤ r) :
    (Nat.card (CFSG.Models.TwistedA r q) * Nat.card (Outer (CFSG.Models.TwistedA r q))) ^ 3 ≤
      5 ^ (q.order ^ r - 1) := by
  have h := Nat.pow_le_pow_left (unitary_component_le_field_power r hr q hsmall hnc) 3
  have he : (q.order ^ unitaryExponent r) ^ 3 = q.order ^ (3 * unitaryExponent r) := by
    rw [←pow_mul, Nat.mul_comm]
  exact (h.trans_eq he).trans (unitary_order_cube q.order r (field_two_le q) hr hcapacity)

private theorem typeA_root_power_ge (q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hc : 7 ≤ q ∨ (4 ≤ q ∧ 3 ≤ r) ∨ (3 ≤ q ∧ 4 ≤ r) ∨ 7 ≤ r) : 32 ≤ q ^ r := by
  rcases hc with h | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · exact (by decide : 32 ≤ 7 ^ 2).trans
      ((Nat.pow_le_pow_left h 2).trans (Nat.pow_le_pow_right (by omega) hr))
  · exact (by decide : 32 ≤ 4 ^ 3).trans
      ((Nat.pow_le_pow_left h 3).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 3 ^ 4).trans
      ((Nat.pow_le_pow_left h 4).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 2 ^ 7).trans
      ((Nat.pow_le_pow_left hq 7).trans (Nat.pow_le_pow_right (by omega) h))

private theorem unitary_root_power_ge (q r : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hc : 10 ≤ q ∨ (5 ≤ q ∧ 3 ≤ r) ∨ (4 ≤ q ∧ 4 ≤ r) ∨
      (3 ≤ q ∧ 5 ≤ r) ∨ 8 ≤ r) : 32 ≤ q ^ r := by
  rcases hc with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · exact (by decide : 32 ≤ 10 ^ 2).trans
      ((Nat.pow_le_pow_left h 2).trans (Nat.pow_le_pow_right (by omega) hr))
  · exact (by decide : 32 ≤ 5 ^ 3).trans
      ((Nat.pow_le_pow_left h 3).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 4 ^ 4).trans
      ((Nat.pow_le_pow_left h 4).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 3 ^ 5).trans
      ((Nat.pow_le_pow_left h 5).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 32 ≤ 2 ^ 8).trans
      ((Nat.pow_le_pow_left hq 8).trans (Nat.pow_le_pow_right (by omega) h))

theorem typeA_order_ge_1024 (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)]
    (hcapacity : 7 ≤ q.order ∨ (4 ≤ q.order ∧ 3 ≤ r) ∨ (3 ≤ q.order ∧ 4 ≤ r) ∨ 7 ≤ r) :
    1024 ≤ Nat.card (CFSG.Models.A r q) := by
  obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.A r q)
  have hlo := (typeA_root_power_ge q.order r (field_two_le q) hr hcapacity).trans
    (CFSGTypeAMinimumIndexLower.order_power_le_leastProperIndex r hr q ell hell)
  have hs := CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card r hr q ell hell
  have hp := Nat.pow_le_pow_left hlo 2
  norm_num only [Nat.reducePow] at hp
  omega

theorem unitary_order_ge_1024 (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r = 2 → q.order ≠ 2) [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hcapacity : 10 ≤ q.order ∨ (5 ≤ q.order ∧ 3 ≤ r) ∨ (4 ≤ q.order ∧ 4 ≤ r) ∨
      (3 ≤ q.order ∧ 5 ≤ r) ∨ 8 ≤ r) :
    1024 ≤ Nat.card (CFSG.Models.TwistedA r q) := by
  obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.TwistedA r q)
  have hlo := (unitary_root_power_ge q.order r (field_two_le q) hr hcapacity).trans
    (twistedA_admissible_order_power_le_leastProperIndex r hr q hsmall ell hell)
  have hs := twistedA_admissible_leastIndex_square_lt r hr q hsmall ell hell
  have hp := Nat.pow_le_pow_left hlo 2
  norm_num only [Nat.reducePow] at hp
  omega

end SymmetricSubgroupAsymptotics.CFSGTypeAUnitaryComponentOrderCube
