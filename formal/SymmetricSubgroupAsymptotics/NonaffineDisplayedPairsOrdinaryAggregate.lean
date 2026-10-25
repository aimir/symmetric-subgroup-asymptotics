import SymmetricSubgroupAsymptotics.ImprimitiveMinimumRateScaling
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! A shared scalar aggregate for two actual local generating pairs.
The quotient coefficient remains explicit, and the rounded top ceiling
is paid at every top degree. The local-degree tail is an induction, not
an action census or a supplied fitting condition. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineDisplayedPairsOrdinaryAggregate
open ActualWreathChiefUnitMinimumRate

/-- One quadratic dyadic budget controls the whole infinite scalar tail. -/
theorem dyadic_budget (m : ℕ) (hm : 5 ≤ m) : (m+2)*(m+8) ≤ 3*2^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hstep : (m+3)*(m+9) ≤ 2*((m+2)*(m+8)) := by nlinarith only [hm]
    calc
      (m+1+2)*(m+1+8) ≤ 2*((m+2)*(m+8)) := by simpa only [Nat.add_assoc] using hstep
      _ ≤ 2*(3*2^m) := Nat.mul_le_mul_left 2 ih
      _ = 3*2^(m+1) := by rw [pow_succ]; omega

/-- Two pair heads and a twice-log quotient coefficient fit every local
degree at least 25. This theorem is purely scalar. -/
theorem local_degree_margin (r : ℕ) (hr : 25 ≤ r) :
    2*Real.sqrt (Real.logb 2 (r : ℝ)+1)+
      (Real.logb 2 (r : ℝ)+1)*Real.sqrt (Real.logb 2 (r : ℝ)+4) ≤ (r : ℝ) := by
  let L := Real.logb 2 (r : ℝ)
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r by omega))
  by_cases hs : r < 32
  · have hLu : L ≤ 5 := by
      have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 5
        (by omega) (by decide) (by simpa only [pow_one] using (show r ≤ 2^5 by omega))
      simpa only [Nat.cast_one,div_one] using hh
    have hroot1 : Real.sqrt (L+1) ≤ 5/2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [hLu]⟩
    have hroot4 : Real.sqrt (L+4) ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [hLu]⟩
    have hprod' := mul_le_mul_of_nonneg_left hroot4 (show 0 ≤ L+1 by linarith only [hL])
    have hrR : (25 : ℝ) ≤ r := by exact_mod_cast hr
    change 2*Real.sqrt (L+1)+(L+1)*Real.sqrt (L+4) ≤ (r : ℝ)
    nlinarith only [hroot1,hprod',hLu,hrR]
  · let m := Nat.log 2 r
    have hm : 5 ≤ m := Nat.le_log_of_pow_le (by decide : 1 < 2)
      (show 2^5 ≤ r by omega)
    have hp : (2 : ℝ)^m ≤ (r : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (show r ≠ 0 by omega)
    have hLu : L ≤ (m : ℝ)+1 := by
      have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 (m+1)
        (by omega) (by decide)
        (by simpa only [pow_one] using (Nat.lt_pow_succ_log_self (by decide : 1 < 2) r).le)
      simpa only [Nat.cast_add,Nat.cast_one,div_one] using hh
    have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
    have hroot1 : Real.sqrt (L+1) ≤ ((m : ℝ)+2)/2 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith only [hLu,hmR,sq_nonneg ((m : ℝ)-5)]
    have hroot4 : Real.sqrt (L+4) ≤ ((m : ℝ)+5)/3 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith only [hLu,hmR,sq_nonneg ((m : ℝ)-5)]
    have hprod := mul_le_mul (show L+1 ≤ (m : ℝ)+2 by linarith only [hLu]) hroot4
      (Real.sqrt_nonneg (L+4)) (by positivity : (0 : ℝ) ≤ (m : ℝ)+2)
    have hbudget : ((m : ℝ)+2)*((m : ℝ)+8) ≤ 3*(2 : ℝ)^m := by
      exact_mod_cast dyadic_budget m hm
    change 2*Real.sqrt (L+1)+(L+1)*Real.sqrt (L+4) ≤ (r : ℝ)
    nlinarith only [hroot1,hprod,hbudget,hp]

/-- A real ordinary cost with two pair heads, its actual quotient
coefficient and its actual rounded top ceiling fits the product degree. -/
theorem two_pair_cost_le (r t : ℕ) (hr : 25 ≤ r) (ht : 2 ≤ t)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 2*Real.logb 2 (r : ℝ)) :
    4+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  let L := Real.logb 2 (r : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let w := Real.sqrt (L+e)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r by omega))
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL he)
  have htop := ImprimitiveMinimumRateScaling.ceiling_le_twice_rate t ht
  have hhead := ImprimitiveTopLogarithmicScaling.sqrt_log_add_le_half_mul L hL t ht
  have hrate := mul_le_mul_of_nonneg_left
    (ImprimitiveMinimumRateScaling.rate_mul_sqrt_log_add_le L hL t ht)
    (show 0 ≤ b+2 by linarith only [hb0])
  have hsource := mul_le_mul_of_nonneg_right htop (Real.sqrt_nonneg (L+e))
  have hcoeff := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (t : ℝ)/2*Real.sqrt (L+4) by positivity)
  have hscaled : (4+b*rate t+traceyPermutationGeneratorCeiling t)*w ≤
      (t : ℝ)*(2*Real.sqrt (L+1)+(L+1)*Real.sqrt (L+4)) := by
    nlinarith only [hsource,hhead,hrate,hcoeff]
  have hmargin := mul_le_mul_of_nonneg_left (local_degree_margin r hr)
    (show (0 : ℝ) ≤ t by positivity)
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change 4+b*rate t+traceyPermutationGeneratorCeiling t ≤ (r : ℝ)*(t : ℝ)/w
  apply (le_div_iff₀ hw).mpr
  nlinarith only [hscaled,hmargin]

end SymmetricSubgroupAsymptotics.NonaffineDisplayedPairsOrdinaryAggregate
