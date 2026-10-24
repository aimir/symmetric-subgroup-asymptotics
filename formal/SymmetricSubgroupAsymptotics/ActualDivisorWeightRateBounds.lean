import SymmetricSubgroupAsymptotics.ActualWreathChiefDivisorWeights
import Mathlib.Algebra.Order.Ring.Pow

/-! The actual prime-power divisor rates already dominate one. Thus
replacing a constructed divisor weight by its raw rate retains the floor
one paying genuine nonabelian ordinary ranks; it is never discarded as
an asymptotic error. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualDivisorWeightRateBounds
open ActualWreathChiefDivisorWeights

theorem one_le_divisorRate (t q e p : ℕ) (ht : 2 ≤ t) (hq : q.Prime)
    (he : 1 ≤ e) (hd : q^e ∣ t) : 1 ≤ divisorRate t q e p := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hpow : (q : ℝ)^e ≤ t := by
    exact_mod_cast Nat.le_of_dvd (by omega : 0 < t) hd
  unfold divisorRate
  split_ifs
  · have hden : 0 < 3*((q : ℝ)-1)*e :=
      mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
    have hbern := one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ q) e
    have hquad : (2 : ℝ)*(t : ℝ) ≤ (t : ℝ)^2 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ t by linarith)
        (show (0 : ℝ) ≤ (t : ℝ)-2 by linarith)]
    have hnum : 3*((q : ℝ)-1)*e ≤ (t : ℝ)^2*2 := by nlinarith
    have hsquare : (1 : ℝ) ≤
        ((t : ℝ)*Real.sqrt (2/(3*((q : ℝ)-1)*e)))^2 := by
      rw [mul_pow,Real.sq_sqrt (by positivity),←mul_div_assoc]
      exact (le_div_iff₀ hden).mpr (by simpa only [one_mul] using hnum)
    exact (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp (by simpa using hsquare)
  · exact (le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ)^e)).mpr
      (by simpa only [one_mul] using hpow)

theorem divisorWeight_le_divisorRate (t q e p : ℕ) (ht : 2 ≤ t) (hq : q.Prime)
    (he : 1 ≤ e) (hd : q^e ∣ t) : divisorWeight t q e p ≤ divisorRate t q e p := by
  exact max_le (one_le_divisorRate t q e p ht hq he hd)
    ((min_le_right _ _).trans (min_le_right _ _))

theorem min_divisorWeights_le_rate (t q e r f p : ℕ)
    (ht : 2 ≤ t) (hq : q.Prime) (he : 1 ≤ e) (hd : q^e ∣ t)
    (hr : r.Prime) (hf : 1 ≤ f) (hrd : r^f ∣ t) :
    min (divisorWeight t q e p) (divisorWeight t r f p) ≤
      min (divisorRate t q e p) (divisorRate t r f p) := by
  exact min_le_min (divisorWeight_le_divisorRate t q e p ht hq he hd)
    (divisorWeight_le_divisorRate t r f p ht hr hf hrd)

end SymmetricSubgroupAsymptotics.ActualDivisorWeightRateBounds
