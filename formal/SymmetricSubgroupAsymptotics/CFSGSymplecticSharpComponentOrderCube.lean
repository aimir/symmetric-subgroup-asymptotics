import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpOrderUpper
import SymmetricSubgroupAsymptotics.SymplecticSharpOrderCubeNumerics
import SymmetricSubgroupAsymptotics.CFSGSymplecticProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGSymplecticLeastIndexSquare
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart

/-! Sharper native-C component cubes from the actual hyperbolic-pair
order formula, actual outer reconstruction and the unchanged q^(r-1)
proper-index star. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
open CFSGReduction PrimitiveSocleRawStructure CFSGSymplecticSharpOrderUpper
open SymplecticSharpOrderCubeNumerics

private theorem field_two_le (q : CFSG.PrimePower) : 2≤q.order :=
  q.prime_isPrime.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)

theorem component_le_field_power (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)] :
    Nat.card (CFSG.Models.C r q)*Nat.card (Outer (CFSG.Models.C r q))≤q.order^(2*r^2+r+3) := by
  have hf : q.exponent≤q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hc : 3≤q.order^2 := (by decide : 3≤2^2).trans (Nat.pow_le_pow_left (field_two_le q) 2)
  have ho : Nat.card (Outer (CFSG.Models.C r q))≤3*q.exponent := by
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
      typeC_outer_card_le r hr q
  have houter : Nat.card (Outer (CFSG.Models.C r q))≤q.order^3 :=
    (ho.trans (Nat.mul_le_mul hc hf)).trans_eq (pow_succ q.order 2).symm
  exact (Nat.mul_le_mul (typeC_order_le_quadratic_power r hr q) houter).trans_eq (pow_add _ _ _).symm

theorem component_order_cube (r : ℕ) (hr : 3≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)] (hc : Capacity q.order (r-1)) :
    (Nat.card (CFSG.Models.C r q)*Nat.card (Outer (CFSG.Models.C r q)))^3≤5^(q.order^(r-1)-1) := by
  have hs : r-1+1=r := by omega
  have he : 2*r^2+r+3=componentExponent (r-1) := by unfold componentExponent; rw [hs]
  have hp := Nat.pow_le_pow_left (component_le_field_power r (by omega) q) 3
  rw [he,←pow_mul,Nat.mul_comm (componentExponent (r-1)) 3] at hp
  exact hp.trans (common_order_cube q.order (r-1) (field_two_le q) (by omega) hc)

theorem rank_two_component_order_cube (q : CFSG.PrimePower) (hq : 128≤q.order)
    [IsSimpleGroup (CFSG.Models.C 2 q)] :
    (Nat.card (CFSG.Models.C 2 q)*Nat.card (Outer (CFSG.Models.C 2 q)))^3≤5^(q.order-1) := by
  have hp := Nat.pow_le_pow_left (component_le_field_power 2 (by decide) q) 3
  have he : (q.order^(2*2^2+2+3))^3=q.order^39 := by rw [←pow_mul]; norm_num
  exact (hp.trans_eq he).trans (rank_two_order_cube q.order hq)

theorem order_ge_1024_of_star (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)] (hstar : 32≤q.order^(r-1)) :
    1024≤Nat.card (CFSG.Models.C r q) := by
  have hsmall : r=2 → q.order≠2 := by
    intro hh he
    have hb : 32≤2 := by simpa only [hh,he,Nat.reduceSub,pow_one] using hstar
    omega
  obtain ⟨ell,hell⟩ := exists_leastProperIndex (CFSG.Models.C r q)
  have hlo := hstar.trans (typeC_order_power_le_leastProperIndex r hr q ell hell)
  have hs := typeC_leastProperIndex_square_lt_card r q hr hsmall ell hell
  have hp := Nat.pow_le_pow_left hlo 2
  norm_num only [Nat.reducePow] at hp
  omega

end SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
