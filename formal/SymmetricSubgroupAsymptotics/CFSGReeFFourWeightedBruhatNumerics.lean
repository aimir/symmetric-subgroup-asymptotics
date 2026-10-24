import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Numerical budget for the sixteen alternating relative Weyl words.
The two simple inversion weights are q and q². This module proves only
the polynomial identity and its torus-weighted budget; it assumes no
Bruhat-cell parametrization or group-order conclusion. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedBruhatNumerics

def weightedMenu (q : ℕ) : ℕ :=
  1 + q + q^2 + 2*q^3 + q^4 + q^5 + 2*q^6 + q^7 + q^8 +
    2*q^9 + q^10 + q^11 + q^12

theorem weightedMenu_factor (q : ℕ) :
    weightedMenu q = (1+q)*(1+q^2)*(1+q^3)*(1+q^6) := by
  unfold weightedMenu
  ring

theorem torus_weightedMenu_le (q : ℕ) (hq : 2 ≤ q) :
    (q-1)^2 * weightedMenu q ≤ q^14 := by
  have hq1 : 1 ≤ q := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq31 : (q : ℝ) ≤ (q : ℝ)^3 := by
    exact_mod_cast (Nat.le_self_pow (by norm_num : 3 ≠ 0) q)
  have hq46 : (q : ℝ)^4 ≤ (q : ℝ)^6 := by
    exact_mod_cast (Nat.pow_le_pow_right hq1 (by norm_num : 4 ≤ 6))
  have hfirst : ((q : ℝ)-1)*((q : ℝ)^3+1) ≤ (q : ℝ)^4 := by nlinarith
  have hsecond : ((q : ℝ)^4-1)*((q : ℝ)^6+1) ≤ (q : ℝ)^10 := by nlinarith
  have hq4 : (1 : ℝ) ≤ (q : ℝ)^4 := one_le_pow₀ hqR
  have hprod := mul_le_mul hfirst hsecond
    (mul_nonneg (sub_nonneg.mpr hq4) (by positivity)) (by positivity : (0 : ℝ) ≤ (q : ℝ)^4)
  have hidentity : (((q-1)^2*weightedMenu q : ℕ) : ℝ) =
      (((q : ℝ)-1)*((q : ℝ)^3+1))*(((q : ℝ)^4-1)*((q : ℝ)^6+1)) := by
    rw [weightedMenu_factor]
    push_cast [Nat.cast_sub hq1]
    ring
  rw [←hidentity] at hprod
  have hpow : (q : ℝ)^4*(q : ℝ)^10 = ((q^14 : ℕ) : ℝ) := by push_cast; ring
  rw [hpow] at hprod
  exact_mod_cast hprod

theorem positive_torus_weightedMenu_le (q : ℕ) (hq : 2 ≤ q) :
    q^12 * (q-1)^2 * weightedMenu q ≤ q^26 := by
  calc
    _ = q^12*((q-1)^2*weightedMenu q) := by ring
    _ ≤ q^12*q^14 := Nat.mul_le_mul_left _ (torus_weightedMenu_le q hq)
    _ = _ := by ring

end SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedBruhatNumerics
