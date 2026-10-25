import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePairingIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleScalarIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSharpComponentOrderBudget
import SymmetricSubgroupAsymptotics.GTwoMiddlePairingClassNumerics
import SymmetricSubgroupAsymptotics.GTwoEndpointOrbitClassNumerics

/-! The already proved original G2 proper indices pay the SAME original
order-times-outer cube for the whole admissible family. The four field
regimes reuse the actual source index packets; no permutation action,
class-capacity hypothesis, or new model identification is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoProperIndexComponentCube
open PrimitiveSocleRawStructure

theorem order_mul_outer_cube_le_proper_index (q : CFSG.PrimePower) (hs : q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.G2 q)] (hn : ¬IsMulCommutative (CFSG.Models.G2 q))
    (H : Subgroup (CFSG.Models.G2 q)) (hH : H ≠ ⊤) :
    (Nat.card (CFSG.Models.G2 q)*Nat.card (Outer (CFSG.Models.G2 q)))^3 ≤
      5^(H.index-1) := by
  have htwo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  by_cases hthree : q.order = 3
  · have hp3 : q.prime ∣ 3^1 := by
      change q.prime ∣ 3
      rw [← hthree]
      exact dvd_pow_self _ q.exponent_pos.ne'
    have hp : q.prime = 3 :=
      Nat.prime_eq_prime_of_dvd_pow q.prime_isPrime (by decide) hp3
    have hf : q.exponent = 1 := Nat.pow_right_injective (by decide : 2 ≤ 3)
      (by simpa only [CFSG.PrimePower.order, hp] using hthree)
    have hi := CFSGGTwoCharacteristicThreeMiddleIndex.typeGTwo_field_three_le_proper_index
      q hthree H hH
    have hc := Nat.pow_le_pow_left (Nat.mul_le_mul
      (CFSGGTwoD4GeckFixedBruhatOrderUpper.typeGTwo_order_le q hn)
      (CFSGGTwoD4GeckOriginalOuterBound.typeGTwo_outer_card_le_two_exponent q)) 3
    have hb : (24*q.exponent*q.order^14*(2*q.exponent))^3 ≤ 5^(54-1) := by
      rw [hthree, hf]
      decide +kernel
    exact (hc.trans hb).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hi 1))
  by_cases hfour : q.order = 4
  · have hp4 : q.prime ∣ 2^2 := by
      change q.prime ∣ 4
      rw [← hfour]
      exact dvd_pow_self _ q.exponent_pos.ne'
    have hp : q.prime = 2 :=
      Nat.prime_eq_prime_of_dvd_pow q.prime_isPrime (by decide) hp4
    have hf : q.exponent = 2 := Nat.pow_right_injective (by decide : 2 ≤ 2)
      (by simpa only [CFSG.PrimePower.order, hp] using hfour)
    have hi := CFSGGTwoD4GeckMiddleScalarIndex.typeGTwo_scalar_le_proper_index
      q (by omega) H hH
    rw [hfour] at hi
    have hc := Nat.pow_le_pow_left (Nat.mul_le_mul
      (CFSGGTwoD4GeckFixedBruhatOrderUpper.typeGTwo_order_le q hn)
      (CFSGGTwoD4GeckOriginalOuterBound.typeGTwo_outer_card_le_two_exponent q)) 3
    have hb : (24*q.exponent*q.order^14*(2*q.exponent))^3 ≤ 5^(48-1) := by
      rw [hfour, hf]
      decide +kernel
    exact (hc.trans hb).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hi 1))
  have hfive : 5 ≤ q.order := by omega
  have hc := Nat.pow_le_pow_left
    (CFSGGTwoD4GeckSharpComponentOrderBudget.order_mul_outer_le q (by omega) hn) 3
  by_cases hchar : q.prime = 3
  · have hd : 3 ∣ q.order := by
      rw [← hchar]
      exact dvd_pow_self _ q.exponent_pos.ne'
    have hsix : 6 ≤ q.order := by obtain ⟨t, ht⟩ := hd; omega
    have hi := CFSGGTwoD4GeckMiddleEndpointIndex.typeGTwo_char_three_le_proper_index
      q hchar (by omega) H hH
    have hb : (q.order^20)^3 ≤ 5^(3*(q.order^2-1)-1) := by
      simpa only [← pow_mul] using
        GTwoEndpointOrbitClassNumerics.endpoint_orbit_budget q.order hsix
    exact (hc.trans hb).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hi 1))
  · have hi := CFSGGTwoD4GeckMiddlePairingIndex.typeGTwo_middle_le_proper_index q hchar H hH
    have hb : (q.order^20)^3 ≤ 5^(q.prime*q.order^2-1) := by
      simpa only [← pow_mul] using
        GTwoMiddlePairingClassNumerics.primePower_middle_index_budget q hfive
    exact (hc.trans hb).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hi 1))

end SymmetricSubgroupAsymptotics.CFSGGTwoProperIndexComponentCube
