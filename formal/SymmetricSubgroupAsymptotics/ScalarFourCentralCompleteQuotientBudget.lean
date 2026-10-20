import SymmetricSubgroupAsymptotics.ScalarFourCentralCompleteQuotientSum
import SymmetricSubgroupAsymptotics.ScalarFourCentralOrderBound
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators

/-! Uniform constants for the actual all-normal cubic central-repeat sum. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu

 theorem coldSlope_le_common : coldSlope≤(381/192 : ℝ) := by
  have hp : ((5 : ℝ)^3)<(2 : ℝ)^(7 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2)
    (pow_pos (by norm_num) 3) hp
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] at hl
  unfold coldSlope
  norm_num at hl ⊢
  linarith

theorem cubicColdCoefficient_sixteen_le : cubicColdCoefficient 16≤(2 : ℝ)^64 := by
  have hc : Nat.card CyclicThree=3 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    simp
  have ha : Nat.card (CyclicThree ≃* CyclicThree)≤27 := by
    calc
      _ ≤ Nat.card (CyclicThree → CyclicThree) :=
        Nat.card_le_card_of_injective (fun e : CyclicThree ≃* CyclicThree =>
          (e : CyclicThree → CyclicThree)) DFunLike.coe_injective
      _ = _ := by rw [Nat.card_fun,hc]; norm_num
  have ha' : (Nat.card (CyclicThree ≃* CyclicThree) : ℝ)≤27 := by exact_mod_cast ha
  calc
    cubicColdCoefficient 16 ≤ 27*((2 : ℝ)^16)^3 :=
      mul_le_mul_of_nonneg_right ha' (by positivity)
    _ ≤ (2 : ℝ)^(64 : ℕ) := by norm_num

variable {Q : Type} [Group Q] [Finite Q] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q CyclicThree c d)

include D

theorem order_le_sixteen (hc : c≤3) (hd : d≤3) : Nat.card Q≤2^16 := by
  have hT : Nat.card CyclicThree=3 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    simp
  have h := D.order_le
  rw [hT] at h
  have h1 := Nat.pow_le_pow_right (by decide : 1≤2) hc
  have h2 := Nat.pow_le_pow_right (by decide : 1≤4) hd
  have hm := Nat.mul_le_mul h1 h2
  norm_num at hm ⊢
  nlinarith

theorem normal_count_le (hc : c≤3) (hd : d≤3) :
    Nat.card {N : Subgroup Q // N.Normal}≤2^256 := by
  simpa using normalSubgroup_card_le_two_pow_sq 16 (D.order_le_sixteen hc hd)

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
