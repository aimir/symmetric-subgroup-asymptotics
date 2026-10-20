import SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceMenu
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4CompleteQuotientBudget
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceMenu
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Finite Q] [Group T] [Finite T]

 theorem aut_card_le (hQ : Nat.card Q≤2^15) : Nat.card (Q ≃* Q)≤2^225 := by
  calc
    _ ≤ Nat.card Q ^ Nat.log 2 (Nat.card Q) := mulEquiv_card_le_card_pow_log Q
    _ ≤ (2^15)^Nat.log 2 (Nat.card Q) := Nat.pow_le_pow_left hQ _
    _ ≤ (2^15)^15 := Nat.pow_le_pow_right (by positivity)
      ((Nat.log_mono_right (b := 2) hQ).trans_eq (Nat.log_pow (by norm_num) 15))
    _ = _ := by rw [←pow_mul]

 theorem binary_coefficient_le {c d : ℕ} (D : ScalarFourCentralTopCoordinates Q T c d)
    (hQ : Nat.card Q≤2^15) (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f) :
    D.coldCoefficient≤(2 : ℝ)^(225 : ℕ) := by
  have hQ16 : Nat.card Q≤2^16 := hQ.trans (by norm_num)
  have hbase : D.coldCoefficient≤ScalarFourCentralC4TopCoordinates.menuColdCoefficient T 16 := by
    unfold ScalarFourCentralTopCoordinates.coldCoefficient ScalarFourCentralC4TopCoordinates.menuColdCoefficient
    rw [Nat.cast_mul,Nat.cast_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hQ16) (Nat.card T)) (by positivity)
  exact hbase.trans ((ScalarFourCentralC4TopCoordinates.menuColdCoefficient_sixteen_le f hf).trans
    (pow_le_pow_right₀ (by norm_num) (by omega)))

 theorem c4_coefficient_le {c d : ℕ} (D : ScalarFourCentralC4TopCoordinates Q T c d)
    (hQ : Nat.card Q≤2^15) (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f) :
    D.coldCoefficient≤(2 : ℝ)^(225 : ℕ) := by
  have hQ16 : Nat.card Q≤2^16 := hQ.trans (by norm_num)
  have hbase : D.coldCoefficient≤ScalarFourCentralC4TopCoordinates.menuColdCoefficient T 16 := by
    unfold ScalarFourCentralC4TopCoordinates.coldCoefficient ScalarFourCentralC4TopCoordinates.menuColdCoefficient
    rw [Nat.cast_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hQ16) (Nat.card T)) (by positivity)
  exact hbase.trans ((ScalarFourCentralC4TopCoordinates.menuColdCoefficient_sixteen_le f hf).trans
    (pow_le_pow_right₀ (by norm_num) (by omega)))

 theorem binary_raw_mono (k b : ℕ) (hk : k≤21) :
    BinaryKernelRankTailNumerics.raw 1 k b≤BinaryKernelRankTailNumerics.raw 1 21 b := by
  unfold BinaryKernelRankTailNumerics.raw
  simp only [one_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hf : (1 : ℝ)≤(b.factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)
  exact pow_le_pow_right₀ hf hk

 theorem c4_raw_mono (k b : ℕ) (hk : k≤21) :
    MarkedC4KernelRankTailNumerics.raw 1 k b≤MarkedC4KernelRankTailNumerics.raw 1 21 b := by
  unfold MarkedC4KernelRankTailNumerics.raw
  simp only [one_mul]
  apply mul_le_mul_of_nonneg_right _ (by unfold markedC4Moment; positivity)
  have hf : (1 : ℝ)≤(b.factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)
  exact pow_le_pow_right₀ hf hk

end SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceMenu
