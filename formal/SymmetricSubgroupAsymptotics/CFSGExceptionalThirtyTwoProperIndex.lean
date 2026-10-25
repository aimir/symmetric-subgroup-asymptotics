import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePairingIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddlePairingIndex
import SymmetricSubgroupAsymptotics.CFSGReeGTwoRectangularPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightPrimeIndex
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiIndex

/-! Every admissible original exceptional Lie model has proper index at
least32. These are thin consequences of actual root, radical or selected
word actions; no finite action census or generator premise is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalThirtyTwoProperIndex

private theorem prime_order_four_ge (q : CFSG.PrimePower) : 32 ≤ q.prime*q.order^4 := by
  calc
    32 = 2*2^4 := by decide
    _ ≤ q.prime*q.order^4 := Nat.mul_le_mul q.prime_isPrime.two_le
      (Nat.pow_le_pow_left (CFSGTwistedAQuadraticTrace.order_two_le q) 4)

theorem typeFFour (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.F4 q)]
    (H : Subgroup (CFSG.Models.F4 q)) (hH : H ≠ ⊤) : 32 ≤ H.index :=
  (prime_order_four_ge q).trans (CFSGFFourE6HeisenbergIndex.typeFFour_heisenberg_le_proper_index q H hH)

theorem typeTriality (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (H : Subgroup (CFSG.Models.TrialityD4 q)) (hH : H ≠ ⊤) : 32 ≤ H.index :=
  (prime_order_four_ge q).trans (CFSGTrialityGeckMiddlePairingIndex.typeTriality_middle_le_proper_index q H hH)

theorem typeGTwo (q : CFSG.PrimePower) (hs : q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.G2 q)] (H : Subgroup (CFSG.Models.G2 q)) (hH : H ≠ ⊤) :
    32 ≤ H.index := by
  by_cases hq : q.order = 3
  · exact (by decide : 32 ≤ 54).trans
      (CFSGGTwoCharacteristicThreeMiddleIndex.typeGTwo_field_three_le_proper_index q hq H hH)
  have hq4 : 4 ≤ q.order := by
    have hh := CFSGTwistedAQuadraticTrace.order_two_le q
    omega
  have hpow : 16 ≤ q.order^2 := Nat.pow_le_pow_left hq4 2
  by_cases hp : q.prime = 3
  · have hi := CFSGGTwoD4GeckMiddleEndpointIndex.typeGTwo_char_three_le_proper_index q hp hq4 H hH
    omega
  · calc
      32 = 2*16 := by decide
      _ ≤ q.prime*q.order^2 := Nat.mul_le_mul q.prime_isPrime.two_le hpow
      _ ≤ H.index := CFSGGTwoD4GeckMiddlePairingIndex.typeGTwo_middle_le_proper_index q hp H hH

theorem typeESix (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E6 q)]
    (H : Subgroup (CFSG.Models.E6 q)) (hH : H ≠ ⊤) : 32 ≤ H.index :=
  (by decide : 32 ≤ 2048).trans (CFSGReduction.typeE6_2048_le_index q H hH)

theorem typeESeven (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E7 q)]
    (H : Subgroup (CFSG.Models.E7 q)) (hH : H ≠ ⊤) : 32 ≤ H.index :=
  (by decide : 32 ≤ 2048).trans (CFSGReduction.typeE7_2048_le_index q H hH)

theorem typeEEight (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E8 q)]
    (H : Subgroup (CFSG.Models.E8 q)) (hH : H ≠ ⊤) : 32 ≤ H.index :=
  (by decide : 32 ≤ 2048).trans (CFSGReduction.typeE8_2048_le_index q H hH)

theorem typeTwistedESix (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (H : Subgroup (CFSG.Models.TwistedE6 q)) (hH : H ≠ ⊤) : 32 ≤ H.index :=
  (by decide : 32 ≤ 2048).trans (CFSGTwistedE6HeisenbergIndex.proper_index_ge_2048 q H hH)

theorem typeReeGTwo (m : ℕ) (hm : 1 ≤ m) [IsSimpleGroup (CFSG.Models.ReeG2 m)]
    (H : Subgroup (CFSG.Models.ReeG2 m)) (hH : H ≠ ⊤) : 32 ≤ H.index := by
  have hpow : 27 ≤ 3^(2*m+1) := Nat.pow_le_pow_right (by decide : 0 < 3) (show 3 ≤ 2*m+1 by omega)
  have hi := CFSGReeGTwoRectangularPermutationDegree.three_field_card_le_proper_index m hm H hH
  omega

theorem typeReeFFour (m : ℕ) (hm : 1 ≤ m) [IsSimpleGroup (CFSG.Models.ReeF4 m)]
    (H : Subgroup (CFSG.Models.ReeF4 m)) (hH : H ≠ ⊤) : 32 ≤ H.index := by
  by_cases he : m = 1
  · subst m
    exact (by decide : 32 ≤ 109).trans (CFSGReeFFourFieldEightPrimeIndex.proper_index_le H hH)
  have hm2 : 2 ≤ m := by omega
  have hpow : 32 ≤ 2^(2*m+1) := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 2*m+1 by omega)
  have hpow' : 8 ≤ 2^(m+1) := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ m+1 by omega)
  have hi := CFSGReeFFourMiddleSuzukiIndex.middle_suzuki_le_proper_index m (by omega) H hH
  have hprod : 248 ≤ (2^(2*m+1)-1)*2^(m+1) := by
    calc
      248 = (32-1)*8 := by decide
      _ ≤ _ := Nat.mul_le_mul (by omega) hpow'
  omega

end SymmetricSubgroupAsymptotics.CFSGExceptionalThirtyTwoProperIndex
