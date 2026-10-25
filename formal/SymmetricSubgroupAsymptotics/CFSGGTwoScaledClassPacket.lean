import SymmetricSubgroupAsymptotics.QuadraticExponentialPolynomialTail
import SymmetricSubgroupAsymptotics.NonabelianSimpleClassOrderHalf
import SymmetricSubgroupAsymptotics.CFSGGTwoProperIndexComponentCube

/-! A scaled class packet for the original G2 model, except field four.
Field three uses the actual index54 and the class-equation saving. The
remaining fields use the actual prime-times-square or endpoint index.
Field four is explicitly excluded: its current index48 packet does not
pay this scaled envelope. No stronger index or class estimate is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoScaledClassPacket
open PrimitiveSocleRawStructure QuadraticExponentialPolynomialTail

theorem scaled_class_cube_le_proper_index_except_four
    (q : CFSG.PrimePower) (hs : q.order ≠ 2) (hfour : q.order ≠ 4)
    [IsSimpleGroup (CFSG.Models.G2 q)] [Finite (CFSG.Models.G2 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.G2 q))
    (K : Subgroup (CFSG.Models.G2 q)) (hK : K ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.G2 q))*
      Nat.card (Outer (CFSG.Models.G2 q)))^3 ≤ 3^K.index := by
  have htwo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  by_cases hthree : q.order=3
  · have hf : q.exponent=1 :=
      (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_three q.exponent_pos.ne'
        (by decide : (1:ℕ) ≠ 0)
        (show q.prime^q.exponent=3^1 by simpa only [pow_one] using hthree)).2
    have horder := CFSGGTwoD4GeckFixedBruhatOrderUpper.typeGTwo_order_le q hn
    rw [hthree,hf] at horder
    have hhalf := NonabelianSimpleClassOrderHalf.twice_class_card_le_order hn
    have hclass : Nat.card (ConjClasses (CFSG.Models.G2 q)) ≤ 12*3^14 := by omega
    have hout : Nat.card (Outer (CFSG.Models.G2 q)) ≤ 2 := by
      simpa only [hf,mul_one] using
        CFSGGTwoD4GeckOriginalOuterBound.typeGTwo_outer_card_le_two_exponent q
    have hcomponent := (Nat.mul_le_mul hclass hout).trans_eq
      (by ring : (12*3^14)*2=24*3^14)
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hcomponent 3)).trans
      (by decide +kernel : 25*(24*(3:ℕ)^14)^3 ≤ 3^54)).trans
      (Nat.pow_le_pow_right (by decide)
        (CFSGGTwoCharacteristicThreeMiddleIndex.typeGTwo_field_three_le_proper_index q hthree K hK))
  have hq : 5 ≤ q.order := by omega
  have hclass : Nat.card (ConjClasses (CFSG.Models.G2 q)) ≤ Nat.card (CFSG.Models.G2 q) :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hcomponent := (Nat.mul_le_mul_right (Nat.card (Outer (CFSG.Models.G2 q))) hclass).trans
    (CFSGGTwoD4GeckSharpComponentOrderBudget.order_mul_outer_le q (by omega) hn)
  have hcube : 25*(Nat.card (ConjClasses (CFSG.Models.G2 q))*
      Nat.card (Outer (CFSG.Models.G2 q)))^3 ≤ 25*q.order^60 := by
    have hh := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hcomponent 3)
    rw [←pow_mul] at hh
    exact hh
  by_cases hchar : q.prime=3
  · have hf : 2 ≤ q.exponent := by
      have hp := q.exponent_pos
      by_contra hh
      have he : q.exponent=1 := by omega
      exact hthree (by change q.prime^q.exponent=3; rw [hchar,he,pow_one])
    have hq9 : 9 ≤ q.order := by
      change 9 ≤ q.prime^q.exponent
      rw [hchar]
      exact Nat.pow_le_pow_right (by decide : 0 < (3:ℕ)) hf
    have hq2 : 81 ≤ q.order^2 := Nat.pow_le_pow_left hq9 2
    have hsub : q.order^2-1+1=q.order^2 := by omega
    have hi : 2*q.order^2 ≤ K.index :=
      (by omega : 2*q.order^2 ≤ 3*(q.order^2-1)).trans
        (CFSGGTwoD4GeckMiddleEndpointIndex.typeGTwo_char_three_le_proper_index
          q hchar (by omega) K hK)
    exact (hcube.trans (scaled_power_sixty_le_three_two_square q.order (by omega))).trans
      (Nat.pow_le_pow_right (by decide) hi)
  · by_cases hcharTwo : q.prime=2
    · have hf : 3 ≤ q.exponent := by
        by_contra hh
        have he : q.exponent ≤ 2 := by omega
        have hsmall : q.order ≤ 4 := by
          change q.prime^q.exponent ≤ 4
          rw [hcharTwo]
          exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) he
        omega
      have hq8 : 8 ≤ q.order := by
        change 8 ≤ q.prime^q.exponent
        rw [hcharTwo]
        exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hf
      have hi := CFSGGTwoD4GeckMiddlePairingIndex.typeGTwo_middle_le_proper_index q hchar K hK
      have hiTwo : 2*q.order^2 ≤ K.index :=
        (congrArg (fun p : ℕ => p*q.order^2) hcharTwo.symm).le.trans hi
      exact (hcube.trans (scaled_power_sixty_le_three_two_square q.order hq8)).trans
        (Nat.pow_le_pow_right (by decide) hiTwo)
    · have hprimeFour : q.prime ≠ 4 := by
        intro hh
        have hp := q.prime_isPrime
        rw [hh] at hp
        exact (by decide : ¬Nat.Prime 4) hp
      have hp5 : 5 ≤ q.prime := by have hp := q.prime_isPrime.two_le; omega
      have hi := (Nat.mul_le_mul_right (q.order^2) hp5).trans
        (CFSGGTwoD4GeckMiddlePairingIndex.typeGTwo_middle_le_proper_index q hchar K hK)
      exact (hcube.trans (scaled_power_sixty_le_three_five_square q.order hq)).trans
        (Nat.pow_le_pow_right (by decide) hi)

end SymmetricSubgroupAsymptotics.CFSGGTwoScaledClassPacket
