import SymmetricSubgroupAsymptotics.ScalarFourCentralC4CompleteQuotientSum
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4OrderBound
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}

 theorem embedded_top_card_le (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f) :
    Nat.card T≤6 := by
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_perm,Nat.card_fin,show Nat.factorial 3=6 by decide] using h

 theorem menuColdCoefficient_sixteen_le (f : T →* Equiv.Perm (Fin 3))
    (hf : Function.Injective f) : menuColdCoefficient T 16≤(2 : ℝ)^(128 : ℕ) := by
  have ht := embedded_top_card_le f hf
  have haut : Nat.card (T ≃* T)≤6^6 := by
    calc
      _ ≤ Nat.card (T → T) := Nat.card_le_card_of_injective
        (fun e : T ≃* T => (e : T → T)) DFunLike.coe_injective
      _ = Nat.card T^Nat.card T := Nat.card_fun
      _ ≤ 6^Nat.card T := Nat.pow_le_pow_left ht _
      _ ≤ 6^6 := Nat.pow_le_pow_right (by decide) ht
  have ha : (Nat.card (T ≃* T) : ℝ)≤(2 : ℝ)^(16 : ℕ) := by
    exact_mod_cast haut.trans (by norm_num : (6 : ℕ)^6≤2^16)
  have hp : ((2 : ℝ)^16)^(Nat.card T)≤((2 : ℝ)^16)^6 :=
    pow_le_pow_right₀ (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)) ht
  calc
    _ ≤ (2 : ℝ)^(16 : ℕ)*((2 : ℝ)^16)^6 := by
      unfold menuColdCoefficient
      exact mul_le_mul ha hp (by positivity) (by positivity)
    _ = (2 : ℝ)^(112 : ℕ) := by rw [←pow_mul,←pow_add]
    _ ≤ (2 : ℝ)^(128 : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)

variable (D : ScalarFourCentralC4TopCoordinates Q T c d)
include D
 theorem order_le_sixteen (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hc : c≤3) (hd : d≤3) : Nat.card Q≤2^16 := by
  have ht := embedded_top_card_le f hf
  exact D.order_le.trans (by
    have h1 : 4^c≤4^3 := Nat.pow_le_pow_right (by decide) hc
    have h2 : 4^d≤4^3 := Nat.pow_le_pow_right (by decide) hd
    have hh := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) ht
    exact hh.trans (by norm_num))

 theorem normal_count_le (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hc : c≤3) (hd : d≤3) : Nat.card {N : Subgroup Q // N.Normal}≤2^256 :=
  normalSubgroup_card_le_two_pow_sq 16 (D.order_le_sixteen f hf hc hd)

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
