import SymmetricSubgroupAsymptotics.WeakClassicalOrderCubeNumerics
import SymmetricSubgroupAsymptotics.CFSGSymplecticProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTwistedDProperIndexOrderBudget

/-! Native classical component order cubes at the proved weak root stars.
The common exponent is evaluated at r-1 for B/C/D and r-2 for twisted D.
No stronger index exponent or group-order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGWeakClassicalComponentOrderCube
open PrimitiveSocleRawStructure WeakClassicalOrderCubeNumerics

private theorem field_two_le (q : CFSG.PrimePower) : 2 ≤ q.order :=
  q.prime_isPrime.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)

private theorem exponent_le_field (q : CFSG.PrimePower) : q.exponent ≤ q.order :=
  q.exponent.lt_two_pow_self.le.trans (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)

private theorem three_exponent_le (q : CFSG.PrimePower) : 3 * q.exponent ≤ q.order ^ 3 := by
  have hc : 3 ≤ q.order ^ 2 := (by decide : 3 ≤ 2 ^ 2).trans
    (Nat.pow_le_pow_left (field_two_le q) 2)
  exact (Nat.mul_le_mul hc (exponent_le_field q)).trans_eq (pow_succ q.order 2).symm

private theorem twentyFour_exponent_le (q : CFSG.PrimePower) : 24 * q.exponent ≤ q.order ^ 6 := by
  have hc : 24 ≤ q.order ^ 5 := (by decide : 24 ≤ 2 ^ 5).trans
    (Nat.pow_le_pow_left (field_two_le q) 5)
  exact (Nat.mul_le_mul hc (exponent_le_field q)).trans_eq (pow_succ q.order 5).symm

theorem capacity_root_power_ge_512 (q t : ℕ) (hq : 2 ≤ q) (ht : 2 ≤ t)
    (hc : Capacity q t) : 512 ≤ q ^ t := by
  rcases hc with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · exact (by decide : 512 ≤ 23 ^ 2).trans
      ((Nat.pow_le_pow_left h 2).trans (Nat.pow_le_pow_right (by omega) ht))
  · exact (by decide : 512 ≤ 8 ^ 3).trans
      ((Nat.pow_le_pow_left h 3).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 512 ≤ 5 ^ 4).trans
      ((Nat.pow_le_pow_left h 4).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 512 ≤ 4 ^ 5).trans
      ((Nat.pow_le_pow_left h 5).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 512 ≤ 3 ^ 6).trans
      ((Nat.pow_le_pow_left h 6).trans (Nat.pow_le_pow_right (by omega) h'))
  · exact (by decide : 512 ≤ 2 ^ 10).trans
      ((Nat.pow_le_pow_left hq 10).trans (Nat.pow_le_pow_right (by omega) h))

theorem typeC_component_le_field_power (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)] :
    Nat.card (CFSG.Models.C r q) * Nat.card (Outer (CFSG.Models.C r q)) ≤ q.order ^ (4*r^2+3) := by
  have ho : Nat.card (Outer (CFSG.Models.C r q)) ≤ 3*q.exponent := by
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
      CFSGReduction.typeC_outer_card_le r hr q
  exact (Nat.mul_le_mul (CFSGReduction.typeC_order_le_matrix_power r hr q)
    (ho.trans (three_exponent_le q))).trans_eq (pow_add _ _ _).symm

theorem typeB_component_le_field_power (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)] :
    Nat.card (CFSG.Models.B r q) * Nat.card (Outer (CFSG.Models.B r q)) ≤ q.order ^ ((2*r+1)^2+3) := by
  exact (Nat.mul_le_mul (CFSGOrthogonalBOriginalMatrixBounds.typeB_order_le_matrix_power r hr q)
    ((CFSGOrthogonalBOriginalMatrixBounds.typeB_outer_card_le_three_exponent r hr q).trans (three_exponent_le q))).trans_eq (pow_add _ _ _).symm

theorem typeD_component_le_field_power (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] :
    Nat.card (CFSG.Models.D r q) * Nat.card (Outer (CFSG.Models.D r q)) ≤ q.order ^ (4*r^2+6) := by
  exact (Nat.mul_le_mul (CFSGOrthogonalDOriginalOrderUpper.typeD_order_le_matrix_power r hr q)
    ((CFSGOrthogonalDProperIndexOrderBudget.typeD_outer_card_le_twentyFour_exponent r hr q).trans (twentyFour_exponent_le q))).trans_eq (pow_add _ _ _).symm

theorem typeC_component_order_cube (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)] (hc : Capacity q.order (r-1)) :
    (Nat.card (CFSG.Models.C r q) * Nat.card (Outer (CFSG.Models.C r q))) ^ 3 ≤
      5 ^ (q.order ^ (r-1) - 1) := by
  have hs : r-1+1=r := by omega
  have he : 4*r^2+3 ≤ componentExponent (r-1) := by
    unfold componentExponent
    nlinarith
  have hb := (typeC_component_le_field_power r (by omega) q).trans
    (Nat.pow_le_pow_right (by have hq := field_two_le q; omega) he)
  have hp := Nat.pow_le_pow_left hb 3
  rw [←pow_mul, Nat.mul_comm (componentExponent (r-1)) 3] at hp
  exact hp.trans (common_order_cube q.order (r-1) (field_two_le q) (by omega) hc)

theorem typeB_component_order_cube (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)] (hc : Capacity q.order (r-1)) :
    (Nat.card (CFSG.Models.B r q) * Nat.card (Outer (CFSG.Models.B r q))) ^ 3 ≤
      5 ^ (q.order ^ (r-1) - 1) := by
  have hs : r-1+1=r := by omega
  have he : (2*r+1)^2+3 ≤ componentExponent (r-1) := by
    unfold componentExponent
    nlinarith
  have hb := (typeB_component_le_field_power r (by omega) q).trans
    (Nat.pow_le_pow_right (by have hq := field_two_le q; omega) he)
  have hp := Nat.pow_le_pow_left hb 3
  rw [←pow_mul, Nat.mul_comm (componentExponent (r-1)) 3] at hp
  exact hp.trans (common_order_cube q.order (r-1) (field_two_le q) (by omega) hc)

theorem typeD_component_order_cube (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] (hc : Capacity q.order (r-1)) :
    (Nat.card (CFSG.Models.D r q) * Nat.card (Outer (CFSG.Models.D r q))) ^ 3 ≤
      5 ^ (q.order ^ (r-1) - 1) := by
  have hs : r-1+1=r := by omega
  have he : 4*r^2+6 ≤ componentExponent (r-1) := by
    unfold componentExponent
    nlinarith
  have hb := (typeD_component_le_field_power r (by omega) q).trans
    (Nat.pow_le_pow_right (by have hq := field_two_le q; omega) he)
  have hp := Nat.pow_le_pow_left hb 3
  rw [←pow_mul, Nat.mul_comm (componentExponent (r-1)) 3] at hp
  exact hp.trans (common_order_cube q.order (r-1) (field_two_le q) (by omega) hc)

theorem typeTwistedD_component_order_cube (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q)) (hc : Capacity q.order (r-2)) :
    (Nat.card (CFSG.Models.TwistedD r q) * Nat.card (Outer (CFSG.Models.TwistedD r q))) ^ 3 ≤
      5 ^ (q.order ^ (r-2) - 1) := by
  have hs : r-2+2=r := by omega
  have he : 4*r^2+4 = componentExponent (r-2) := by unfold componentExponent; rw [hs]
  have hp := Nat.pow_le_pow_left
    (CFSGTwistedDProperIndexOrderBudget.typeTwistedD_order_mul_outer_le_field_power r hr q hn) 3
  rw [he, ←pow_mul, Nat.mul_comm (componentExponent (r-2)) 3] at hp
  exact hp.trans (common_order_cube q.order (r-2) (field_two_le q) (by omega) hc)

theorem typeC_rank_two_component_order_cube (q : CFSG.PrimePower) (hq : 256 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.C 2 q)] :
    (Nat.card (CFSG.Models.C 2 q) * Nat.card (Outer (CFSG.Models.C 2 q))) ^ 3 ≤ 5 ^ (q.order-1) := by
  have hp := Nat.pow_le_pow_left (typeC_component_le_field_power 2 (by decide) q) 3
  have he : (q.order ^ (4*2^2+3)) ^ 3 = q.order ^ 57 := by rw [←pow_mul]; norm_num
  exact (hp.trans_eq he).trans (symplectic_rank_two_order_cube q.order hq)

end SymmetricSubgroupAsymptotics.CFSGWeakClassicalComponentOrderCube
