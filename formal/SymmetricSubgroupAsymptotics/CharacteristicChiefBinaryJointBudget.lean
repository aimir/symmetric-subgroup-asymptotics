import SymmetricSubgroupAsymptotics.CharacteristicChiefOrderProductBound
import Mathlib.Data.Nat.Log

/-! A joint binary order budget on the SAME actual chief profile.
The defining-characteristic dimensions and all remaining dimensions or
genuine simple ranks consume one common order bound. They must not each
be charged the full order independently. No group recognition is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CharacteristicChiefBinaryJointBudget
open ActualWreathCharacteristicChiefProfile CharacteristicChiefFilteredDimensions
open CharacteristicChiefPrimePowerCosts

theorem joint_dimension_le_log {t cost localOrder : ℕ}
    (P : Profile t cost localOrder) :
    dimensionAt 2 P.charges + otherDimensionAt 2 P.charges + P.simpleRank ≤
      Nat.log 2 localOrder := by
  have hh := CharacteristicChiefOrderProductBound.profile_mixed_order_le P 2
  have hp : 2^(dimensionAt 2 P.charges + otherDimensionAt 2 P.charges + P.simpleRank) ≤
      localOrder := by simpa only [pow_add, Nat.add_assoc, Nat.mul_assoc] using hh
  exact Nat.le_log_of_pow_le (by decide : 1 < (2 : ℕ)) hp

theorem joint_dimension_le_log_of_dvd {t cost localOrder M : ℕ}
    (P : Profile t cost localOrder) (hdiv : localOrder ∣ M) (hM : M ≠ 0) :
    dimensionAt 2 P.charges + otherDimensionAt 2 P.charges + P.simpleRank ≤
      Nat.log 2 M :=
  (joint_dimension_le_log P).trans
    (Nat.log_mono_right (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hdiv))

theorem binary_factorization_le_log (M : ℕ) (hM : M ≠ 0) :
    M.factorization 2 ≤ Nat.log 2 M := by
  have hd : 2^(M.factorization 2) ∣ M :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hM).mpr le_rfl
  exact Nat.le_log_of_pow_le (by decide : 1 < (2 : ℕ))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hd)

/-- Optimizing a joint order budget is valid because the central
coefficient is at least one. The bound on the primary dimensions is
structural; no desired total capacity estimate is supplied. -/
theorem cost_le_binary_joint {t cost localOrder M : ℕ}
    (P : Profile t cost localOrder) (e A : ℕ) (ht : t = 2^e)
    (hdiv : localOrder ∣ M) (hM : M ≠ 0)
    (ha : dimensionAt 2 P.charges ≤ A) (hA : A ≤ Nat.log 2 M) :
    (cost : ℝ) ≤ (A : ℝ)*(e.choose (e/2) : ℝ) + (Nat.log 2 M - A : ℕ) := by
  have hh := profile_cost_le_primePower P 2 e Nat.prime_two ht
  simp only [show 2-1 = (1 : ℕ) by omega, mul_one] at hh
  have htR : (t : ℝ) = (2 : ℝ)^e := by exact_mod_cast ht
  have cancel (a b : ℝ) : a*(2 : ℝ)^e*b/(2 : ℝ)^e = a*b := by
    rw [mul_right_comm, mul_div_cancel_right₀ _ (by positivity : (2 : ℝ)^e ≠ 0)]
  rw [htR, cancel] at hh
  have hj := joint_dimension_le_log_of_dvd P hdiv hM
  have hjR : (dimensionAt 2 P.charges : ℝ) + otherDimensionAt 2 P.charges +
      P.simpleRank ≤ Nat.log 2 M := by exact_mod_cast hj
  have haR : (dimensionAt 2 P.charges : ℝ) ≤ A := by exact_mod_cast ha
  have hchoose : (1 : ℝ) ≤ (e.choose (e/2) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.choose_pos (Nat.div_le_self e 2)))
  have hprod := mul_nonneg (sub_nonneg.mpr haR) (sub_nonneg.mpr hchoose)
  rw [Nat.cast_sub hA]
  nlinarith

end SymmetricSubgroupAsymptotics.CharacteristicChiefBinaryJointBudget
