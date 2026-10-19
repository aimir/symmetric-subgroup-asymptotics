import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricCompleteQuotientSum
import SymmetricSubgroupAsymptotics.ScalarFourCentralCompleteQuotientBudget

/-! Uniform actual-order, normal-count and top-map constants for S3 tops. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {T : Type} [Group T] [Finite T]

theorem symmetricColdCoefficient_sixteen_le (e : T ≃* Equiv.Perm (Fin 3)) :
    symmetricColdCoefficient T 16≤(2 : ℝ)^(128 : ℕ) := by
  have hc : Nat.card T=6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    norm_num
  have ha : Nat.card (T ≃* T)≤46656 := by
    calc
      _ ≤ Nat.card (T → T) :=
        Nat.card_le_card_of_injective (fun e : T ≃* T => (e : T → T)) DFunLike.coe_injective
      _ = _ := by rw [Nat.card_fun,hc]; norm_num
  have ha' : (Nat.card (T ≃* T) : ℝ)≤(2 : ℝ)^(16 : ℕ) := by
    have hh : (Nat.card (T ≃* T) : ℝ)≤46656 := by exact_mod_cast ha
    exact hh.trans (by norm_num)
  calc
    symmetricColdCoefficient T 16 ≤ (2 : ℝ)^(16 : ℕ)*((2 : ℝ)^16)^6 :=
      mul_le_mul_of_nonneg_right ha' (by positivity)
    _ = (2 : ℝ)^(112 : ℕ) := by rw [←pow_mul,←pow_add]
    _ ≤ (2 : ℝ)^(128 : ℕ) := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by omega)

variable {Q : Type} [Group Q] [Finite Q] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)

include D

theorem symmetric_order_le_sixteen (e : T ≃* Equiv.Perm (Fin 3))
    (hc : c≤3) (hd : d≤3) : Nat.card Q≤2^16 := by
  have hT : Nat.card T=6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    norm_num
  have h := D.order_le
  rw [hT] at h
  have h1 := Nat.pow_le_pow_right (by decide : 1≤2) hc
  have h2 := Nat.pow_le_pow_right (by decide : 1≤4) hd
  have hm := Nat.mul_le_mul h1 h2
  norm_num at hm ⊢
  nlinarith

theorem symmetric_normal_count_le (e : T ≃* Equiv.Perm (Fin 3))
    (hc : c≤3) (hd : d≤3) : Nat.card {N : Subgroup Q // N.Normal}≤2^256 := by
  simpa using normalSubgroup_card_le_two_pow_sq 16 (D.symmetric_order_le_sixteen e hc hd)

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
