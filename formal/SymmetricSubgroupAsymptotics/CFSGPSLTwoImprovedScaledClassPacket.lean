import SymmetricSubgroupAsymptotics.PSLTwoImprovedScaledClassNumerics
import SymmetricSubgroupAsymptotics.CFSGPSLTwoCharacteristicIndex
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneOddClassCube
import SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenOuterBound
import SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGPSLTwoThreeModFourPermutationDegree

/-! A shared actual PSL2 packet covers all prime fields from11, binary
powers from16 and the two odd powers27/49. Exact original trace-class,
outer and proper-index bounds are used; the six tiny parameters are not
asserted to satisfy this stronger scaled packet. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoImprovedScaledClassPacket
open PrimitiveSocleRawStructure

def FieldProfile (q : CFSG.PrimePower) : Prop :=
  (q.order.Prime ∧ 11≤q.order) ∨ (q.prime=2 ∧ 16≤q.order) ∨
    q.order=27 ∨ q.order=49

theorem scaled_class_cube_le_proper_index (q : CFSG.PrimePower) (hprofile : FieldProfile q)
    [IsSimpleGroup (CFSG.Models.A 1 q)]
    (K : Subgroup (CFSG.Models.A 1 q)) (hK : K≠⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.A 1 q))*
      Nat.card (Outer (CFSG.Models.A 1 q)))^3≤3^K.index := by
  rcases hprofile with ⟨hprime,hq⟩ | ⟨hp,hq⟩ | hq | hq
  · have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q hprime
    have horder : q.order=q.prime := by change q.prime^q.exponent=q.prime; rw [he,pow_one]
    have hp : q.prime≠2 := by omega
    have hc := CFSGTypeARankOneOddClassCube.twice_class_card_le q hp
    have ho : Nat.card (Outer (CFSG.Models.A 1 q))≤2 := by
      simpa only [he,Nat.mul_one] using CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
    have hB : Nat.card (ConjClasses (CFSG.Models.A 1 q))*
        Nat.card (Outer (CFSG.Models.A 1 q))≤q.order+5 := by
      calc
        _≤Nat.card (ConjClasses (CFSG.Models.A 1 q))*2 := Nat.mul_le_mul_left _ ho
        _=2*Nat.card (ConjClasses (CFSG.Models.A 1 q)) := Nat.mul_comm _ _
        _≤q.order+5 := hc
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hB 3)).trans
      (PSLTwoImprovedScaledClassNumerics.prime_field_tail q.order hq)).trans
      (Nat.pow_le_pow_right (by decide)
        (CFSGPSLTwoCharacteristicIndex.field_le_proper_index_of_prime_order q hprime K hK))
  · have horder : q.order=2^q.exponent := by simp only [CFSG.PrimePower.order,hp]
    have hf : 4≤q.exponent := by
      by_contra hh
      have hb := Nat.pow_le_pow_right (by decide : 0<2) (by omega : q.exponent≤3)
      rw [←horder] at hb
      norm_num at hb
      omega
    have hB := Nat.mul_le_mul
      (CFSGTypeARankOneSharpClassCube.typeA_rank_one_class_card_le q)
      (CFSGPSLTwoEvenOuterBound.typeA_rank_one_outer_card q hp)
    have hs := PSLTwoImprovedScaledClassNumerics.binary_power_tail q.exponent hf
    rw [←horder] at hs
    have hindex : q.order≤K.index := by
      simpa only [q.card_field] using
        CFSGPSLTwoEvenPermutationDegree.field_card_le_proper_index (F:=q.Field)
          ((ringChar.eq q.Field q.prime).trans hp) K hK
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hB 3)).trans hs).trans
      (Nat.pow_le_pow_right (by decide) hindex)
  · have hparams : q.prime=3 ∧ q.exponent=3 :=
      Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
        q.exponent_pos.ne' (by decide : (3:ℕ)≠0)
        (show q.prime^q.exponent=3^3 from hq)
    have hc : Nat.card (ConjClasses (CFSG.Models.A 1 q))≤16 := by
      have hh := CFSGTypeARankOneOddClassCube.twice_class_card_le q (by omega)
      omega
    have ho : Nat.card (Outer (CFSG.Models.A 1 q))≤6 := by
      simpa only [hparams.2,Nat.reduceMul] using CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
    have hindex : 27≤K.index := by
      have hh := CFSGPSLTwoThreeModFourPermutationDegree.field_card_le_proper_index
        (F:=q.Field) (by rw [q.card_field,hq]) K hK
      simpa only [q.card_field,hq] using hh
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
      PSLTwoImprovedScaledClassNumerics.twentySeven).trans
      (Nat.pow_le_pow_right (by decide) hindex)
  · have hparams : q.prime=7 ∧ q.exponent=2 :=
      Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 7)
        q.exponent_pos.ne' (by decide : (2:ℕ)≠0)
        (show q.prime^q.exponent=7^2 from hq)
    have hc : Nat.card (ConjClasses (CFSG.Models.A 1 q))≤27 := by
      have hh := CFSGTypeARankOneOddClassCube.twice_class_card_le q (by omega)
      omega
    have ho : Nat.card (Outer (CFSG.Models.A 1 q))≤4 := by
      simpa only [hparams.2,Nat.reduceMul] using CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
    have hindex : 25≤K.index := by
      have hh : q.order≤2*K.index := by
        simpa only [q.card_field] using
          CFSGPSLTwoGeometry.field_card_le_twice_proper_index (F:=q.Field) K hK
      omega
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
      PSLTwoImprovedScaledClassNumerics.fortyNine).trans
      (Nat.pow_le_pow_right (by decide) hindex)

end SymmetricSubgroupAsymptotics.CFSGPSLTwoImprovedScaledClassPacket
