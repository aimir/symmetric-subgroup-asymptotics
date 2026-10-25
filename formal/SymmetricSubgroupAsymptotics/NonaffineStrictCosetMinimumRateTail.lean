import SymmetricSubgroupAsymptotics.NonaffineLocalLargeDegreeOrdinaryAggregate
import SymmetricSubgroupAsymptotics.ImprimitiveMinimumRateScaling

/-! A minimum-rate strict-coset tail starting at LOCAL degree128.
The two alternatives retain the genuine two-head/ONE-head distinction.
All scalar tails are uniform dyadic inductions. No generating-pair,
model order, action census or desired endpoint fit is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineStrictCosetMinimumRateTail
open ActualWreathChiefUnitMinimumRate

private theorem linear_budget (m : ℕ) (hm : 7 ≤ m) : 4*(m+2) ≤ 2^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih => rw [pow_succ]; omega

private theorem cubic_budget (m : ℕ) (hm : 7 ≤ m) : 4*(m+2)^2*(m+5) ≤ 4^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hstep : 4*(m+3)^2*(m+6) ≤ 4*(4*(m+2)^2*(m+5)) := by
      nlinarith only [Nat.zero_le (m^3),Nat.zero_le (m^2),Nat.zero_le m]
    calc
      4*(m+1+2)^2*(m+1+5) ≤ 4*(4*(m+2)^2*(m+5)) := by
        simpa only [Nat.add_assoc] using hstep
      _ ≤ 4*4^m := Nat.mul_le_mul_left _ ih
      _ = 4^(m+1) := by rw [pow_succ]; omega

private theorem one_factor_budget (m : ℕ) (hm : 7 ≤ m) :
    40*(2*m^2+25*m+66) ≤ 108*2^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hstep : 40*(2*(m+1)^2+25*(m+1)+66) ≤ 2*(40*(2*m^2+25*m+66)) := by
      nlinarith only [Nat.zero_le (m^2),Nat.zero_le m]
    calc
      40*(2*(m+1)^2+25*(m+1)+66) ≤ 2*(40*(2*m^2+25*m+66)) := hstep
      _ ≤ 2*(108*2^m) := Nat.mul_le_mul_left _ ih
      _ = 108*2^(m+1) := by rw [pow_succ]; omega

private theorem dyadic_data (r : ℕ) (hr : 128 ≤ r) :
    ∃ m : ℕ, 7 ≤ m ∧ (2 : ℝ)^m ≤ (r : ℝ) ∧
      Real.logb 2 (r : ℝ) ≤ (m : ℝ)+1 := by
  let m := Nat.log 2 r
  have hm : 7 ≤ m := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (show 2^7 ≤ r by simpa only [show (2 : ℕ)^7 = 128 by decide] using hr)
  have hp : (2 : ℝ)^m ≤ (r : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (show r ≠ 0 by omega)
  have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 (m+1)
    (by omega) (by decide)
    (by simpa only [pow_one] using (Nat.lt_pow_succ_log_self (by decide : 1 < 2) r).le)
  exact ⟨m,hm,hp,by simpa only [Nat.cast_add,Nat.cast_one,div_one] using hh⟩

private theorem square_root_margin (r : ℕ) (hr : 128 ≤ r) :
    Real.sqrt (r : ℝ)*Real.sqrt (Real.logb 2 (r : ℝ)+1)+
      (Real.logb 2 (r : ℝ)+1)*Real.sqrt (Real.logb 2 (r : ℝ)+4) ≤ (r : ℝ) := by
  obtain ⟨m,hm,hp,hLu⟩ := dyadic_data r hr
  let L := Real.logb 2 (r : ℝ)
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r by omega))
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hlinear : 4*(L+1) ≤ (r : ℝ) := by
    have hh : 4*((m : ℝ)+2) ≤ (2 : ℝ)^m := by exact_mod_cast linear_budget m hm
    nlinarith only [hh,hLu,hp]
  have hcube : 4*(L+1)^2*(L+4) ≤ (r : ℝ)^2 := by
    have hh : 4*((m : ℝ)+2)^2*((m : ℝ)+5) ≤ (4 : ℝ)^m := by
      exact_mod_cast cubic_budget m hm
    have hfirst : (L+1)^2 ≤ ((m : ℝ)+2)^2 :=
      (sq_le_sq₀ (by linarith only [hL]) (by positivity)).mpr (by linarith only [hLu])
    have hprod := mul_le_mul hfirst (show L+4 ≤ (m : ℝ)+5 by linarith only [hLu])
      (by linarith only [hL] : 0 ≤ L+4) (sq_nonneg ((m : ℝ)+2))
    have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ (2 : ℝ)^m) hr0).mpr hp
    have h4 : (4 : ℝ)^m = ((2 : ℝ)^m)^2 := by
      calc
        (4 : ℝ)^m = ((2 : ℝ)^2)^m := by norm_num
        _ = (2 : ℝ)^(2*m) := (pow_mul _ _ _).symm
        _ = (2 : ℝ)^(m*2) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ)^m)^2 := pow_mul _ _ _
    rw [h4] at hh
    nlinarith only [hh,hprod,hsquare]
  have hfirst : Real.sqrt (r : ℝ)*Real.sqrt (L+1) ≤ (r : ℝ)/2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hr0,Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+1)]
    nlinarith only [mul_le_mul_of_nonneg_right hlinear hr0]
  have hsecond : (L+1)*Real.sqrt (L+4) ≤ (r : ℝ)/2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+4)]
    nlinarith only [hcube]
  change Real.sqrt (r : ℝ)*Real.sqrt (L+1)+(L+1)*Real.sqrt (L+4) ≤ (r : ℝ)
  linarith only [hfirst,hsecond]

private theorem one_factor_margin (r : ℕ) (hr : 128 ≤ r) :
    Real.sqrt (Real.logb 2 (r : ℝ)+1)/2+
      (Real.logb 2 (r : ℝ)+5)/2*Real.sqrt (Real.logb 2 (r : ℝ)+4) ≤ 9*(r : ℝ)/40 := by
  obtain ⟨m,hm,hp,hLu⟩ := dyadic_data r hr
  let L := Real.logb 2 (r : ℝ)
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r by omega))
  have hmR : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hroot1 : Real.sqrt (L+1) ≤ ((m : ℝ)+2)/2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hLu,hmR,sq_nonneg ((m : ℝ)-7)]
  have hroot4 : Real.sqrt (L+4) ≤ ((m : ℝ)+5)/3 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hLu,hmR,sq_nonneg ((m : ℝ)-7)]
  have hprod := mul_le_mul (show L+5 ≤ (m : ℝ)+6 by linarith only [hLu]) hroot4
    (Real.sqrt_nonneg (L+4)) (by positivity : (0 : ℝ) ≤ (m : ℝ)+6)
  have hbudget : 40*(2*(m : ℝ)^2+25*(m : ℝ)+66) ≤ 108*(2 : ℝ)^m := by
    exact_mod_cast one_factor_budget m hm
  change Real.sqrt (L+1)/2+(L+5)/2*Real.sqrt (L+4) ≤ 9*(r : ℝ)/40
  nlinarith only [hroot1,hprod,hbudget,hp]

/-- The actual two strict-coset heads are paid whenever their least-index
square is at most the local degree. Both induced rates are retained. -/
theorem square_root_cost_le (r t : ℕ) (hr : 128 ≤ r) (ht : 2 ≤ t)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 2*Real.logb 2 (r : ℝ)) :
    2*Real.sqrt (r : ℝ)+b*rate t+traceyPermutationGeneratorCeiling t ≤
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
  have hhead := ImprimitiveTopLogarithmicScaling.sqrt_log_add_le_half_mul L hL t ht
  have htop := ImprimitiveMinimumRateScaling.ceiling_le_twice_rate t ht
  have hsource := mul_le_mul_of_nonneg_right htop (Real.sqrt_nonneg (L+e))
  have hrate := mul_le_mul_of_nonneg_left
    (ImprimitiveMinimumRateScaling.rate_mul_sqrt_log_add_le L hL t ht)
    (show 0 ≤ b+2 by linarith only [hb0])
  have hcoeff := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (t : ℝ)/2*Real.sqrt (L+4) by positivity)
  have hmargin := mul_le_mul_of_nonneg_left (square_root_margin r hr)
    (show (0 : ℝ) ≤ t by positivity)
  have hhead' := mul_le_mul_of_nonneg_left hhead (show 0 ≤ 2*Real.sqrt (r : ℝ) by positivity)
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change 2*Real.sqrt (r : ℝ)+b*rate t+traceyPermutationGeneratorCeiling t ≤ (r : ℝ)*(t : ℝ)/w
  apply (le_div_iff₀ hw).mpr
  nlinarith only [hsource,hrate,hcoeff,hhead',hmargin]

/-- When that square exceeds the local degree the actual socle has one
factor. Its ONE strict-coset head and actual linear outer cost fit. -/
theorem one_factor_cost_le (r t ell : ℕ) (hr : 128 ≤ r) (ht : 2 ≤ t)
    (hell : 2 ≤ ell) (hellr : ell ≤ r) (hrpow : r ≤ ell^2)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 3+Real.logb 2 (r : ℝ)) :
    (traceyPermutationGeneratorCeiling ell : ℝ)+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  let L := Real.logb 2 (r : ℝ)
  let l := Real.logb 2 (ell : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let u := Real.sqrt (L+1)
  let v := Real.sqrt l
  let w := Real.sqrt (L+e)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hL7 : 7 ≤ L := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower r 1 7 (by omega) (by decide)
      (by simpa only [pow_one] using hr)
    simpa only [Nat.cast_one,div_one] using hh
  have hL : 0 ≤ L := by linarith only [hL7]
  have hl : 0 < l := Real.logb_pos (by norm_num) (by linarith only [hellR])
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hv : 0 < v := Real.sqrt_pos.mpr hl
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL he)
  have hLl : L ≤ 2*l := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hrR
      (show (r : ℝ) ≤ (ell : ℝ)^2 by exact_mod_cast hrpow)
    simpa only [Real.logb_pow] using hh
  have huv : u ≤ (31/20 : ℝ)*v := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    dsimp only [u,v]
    rw [mul_pow,Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+1),Real.sq_sqrt hl.le]
    nlinarith only [hL7,hLl]
  have hceil : (traceyPermutationGeneratorCeiling ell : ℝ) ≤ (ell : ℝ)/v+1 := by
    change (⌈(ell : ℝ)/v⌉₊ : ℝ) ≤ (ell : ℝ)/v+1
    exact (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (ell : ℝ)/v)).le
  have hmain : (ell : ℝ)/v*u ≤ (31/20 : ℝ)*(r : ℝ) := by
    calc
      (ell : ℝ)/v*u = (ell : ℝ)*u/v := by ring
      _ ≤ (ell : ℝ)*((31/20 : ℝ)*v)/v :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left huv (by positivity)) hv.le
      _ = (31/20 : ℝ)*(ell : ℝ) := by rw [←mul_assoc,mul_div_cancel_right₀ _ hv.ne']; ring
      _ ≤ (31/20 : ℝ)*(r : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hellr) (by norm_num)
  have hheadU : (traceyPermutationGeneratorCeiling ell : ℝ)*u ≤ (31/20 : ℝ)*(r : ℝ)+u := by
    have hh := mul_le_mul_of_nonneg_right hceil (Real.sqrt_nonneg (L+1))
    nlinarith only [hh,hmain]
  have hheadW := mul_le_mul_of_nonneg_left
    (ImprimitiveTopLogarithmicScaling.sqrt_log_add_le_half_mul L hL t ht)
    (show (0 : ℝ) ≤ traceyPermutationGeneratorCeiling ell by positivity)
  have hheadScaled := mul_le_mul_of_nonneg_left hheadU (show 0 ≤ (t : ℝ)/2 by positivity)
  have htop := ImprimitiveMinimumRateScaling.ceiling_le_twice_rate t ht
  have hsource := mul_le_mul_of_nonneg_right htop (Real.sqrt_nonneg (L+e))
  have hrate := mul_le_mul_of_nonneg_left
    (ImprimitiveMinimumRateScaling.rate_mul_sqrt_log_add_le L hL t ht)
    (show 0 ≤ b+2 by linarith only [hb0])
  have hcoeff := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (t : ℝ)/2*Real.sqrt (L+4) by positivity)
  have hmargin := mul_le_mul_of_nonneg_left (one_factor_margin r hr)
    (show (0 : ℝ) ≤ t by positivity)
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change (traceyPermutationGeneratorCeiling ell : ℝ)+b*rate t+traceyPermutationGeneratorCeiling t ≤
    (r : ℝ)*(t : ℝ)/w
  apply (le_div_iff₀ hw).mpr
  nlinarith only [hheadW,hheadScaled,hsource,hrate,hcoeff,hmargin]

end SymmetricSubgroupAsymptotics.NonaffineStrictCosetMinimumRateTail
