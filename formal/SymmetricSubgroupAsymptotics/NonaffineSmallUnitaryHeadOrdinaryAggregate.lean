import SymmetricSubgroupAsymptotics.ImprimitiveMinimumRateScaling
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity

/-! Uniform small ordinary-head bands, retaining actual quotient rate
and actual coarse top ceiling. The only top split singles out degree2,
where rounding is exact; there is no list of group actions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineSmallUnitaryHeadOrdinaryAggregate
open ActualWreathChiefUnitMinimumRate

private theorem cost_of_constants (r t lo : ℕ) (hr : 2 ≤ r) (ht : 2 ≤ t) (hlo : lo ≤ r)
    (H b U Hmax Bmax c1 c4 : ℝ) (hH0 : 0 ≤ H) (hb0 : 0 ≤ b)
    (hH : H ≤ Hmax) (hb : b ≤ Bmax) (hLU : Real.logb 2 (r : ℝ) ≤ U)
    (hc1 : 0 ≤ c1) (hc4 : 0 ≤ c4) (hsq1 : U+1 ≤ c1^2) (hsq4 : U+4 ≤ c4^2)
    (hc : Hmax/2*c1+(Bmax+2)/2*c4 ≤ (lo : ℝ)) :
    H+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  let L := Real.logb 2 (r : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let u1 := Real.sqrt (L+1)
  let u4 := Real.sqrt (L+4)
  let w := Real.sqrt (L+e)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r by omega))
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL he)
  have hroot1 : u1 ≤ c1 := Real.sqrt_le_iff.mpr ⟨hc1,by linarith only [hLU,hsq1]⟩
  have hroot4 : u4 ≤ c4 := Real.sqrt_le_iff.mpr ⟨hc4,by linarith only [hLU,hsq4]⟩
  have hh1 := mul_le_mul hH hroot1 (Real.sqrt_nonneg (L+1))
    (show 0 ≤ Hmax by linarith only [hH0,hH])
  have hh4 := mul_le_mul (show b+2 ≤ Bmax+2 by linarith only [hb]) hroot4
    (Real.sqrt_nonneg (L+4)) (show 0 ≤ Bmax+2 by linarith only [hb0,hb])
  have hloR : (lo : ℝ) ≤ r := by exact_mod_cast hlo
  have hmargin : H/2*u1+(b+2)/2*u4 ≤ (r : ℝ) := by nlinarith only [hh1,hh4,hc,hloR]
  have hhead := mul_le_mul_of_nonneg_left
    (ImprimitiveTopLogarithmicScaling.sqrt_log_add_le_half_mul L hL t ht) hH0
  have htop := ImprimitiveMinimumRateScaling.ceiling_le_twice_rate t ht
  have hsource := mul_le_mul_of_nonneg_right htop (Real.sqrt_nonneg (L+e))
  have hrate := mul_le_mul_of_nonneg_left
    (ImprimitiveMinimumRateScaling.rate_mul_sqrt_log_add_le L hL t ht)
    (show 0 ≤ b+2 by linarith only [hb0])
  have hscaled := mul_le_mul_of_nonneg_left hmargin (show (0 : ℝ) ≤ t by positivity)
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change H+b*rate t+traceyPermutationGeneratorCeiling t ≤ (r : ℝ)*(t : ℝ)/w
  apply (le_div_iff₀ hw).mpr
  nlinarith only [hhead,hsource,hrate,hscaled]

theorem four_generator_cost_le (r t : ℕ) (hr : 9 ≤ r) (hsmall : r < 16) (ht : 2 ≤ t)
    (H b : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 4) (hb0 : 0 ≤ b) (hb : b ≤ 1) :
    H+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  have hLU : Real.logb 2 (r : ℝ) ≤ 4 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 4 (by omega) (by decide)
      (by simpa only [pow_one] using (show r ≤ 2^4 by omega))
    simpa only [Nat.cast_one,div_one] using hh
  exact cost_of_constants r t 9 (by omega) ht hr H b 4 4 1 (9/4) (17/6)
    hH0 hb0 hH hb hLU (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem seven_generator_cost_le (r t : ℕ) (hr : 16 ≤ r) (hsmall : r < 32) (ht : 2 ≤ t)
    (H b : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 7) (hb0 : 0 ≤ b) (hb : b ≤ 2) :
    H+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  have hLU : Real.logb 2 (r : ℝ) ≤ 5 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 5 (by omega) (by decide)
      (by simpa only [pow_one] using (show r ≤ 2^5 by omega))
    simpa only [Nat.cast_one,div_one] using hh
  exact cost_of_constants r t 16 (by omega) ht hr H b 5 7 2 (5/2) 3
    hH0 hb0 hH hb hLU (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem sqrt_log_add_le_third_mul (L : ℝ) (hL : 0 ≤ L) (t : ℕ) (ht : 3 ≤ t) :
    Real.sqrt (L+Real.logb 2 (t : ℝ)) ≤ (t : ℝ)/3*Real.sqrt (L+2) := by
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have he : 0 ≤ Real.logb 2 (t : ℝ) :=
    Real.logb_nonneg (by norm_num) (by linarith only [htR])
  have hlog := BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one t (by omega)
  have hpoly := mul_nonneg (show 0 ≤ (t : ℝ)-3 by linarith only [htR])
    (show 0 ≤ 2*(t : ℝ)-3 by linarith only [htR])
  have hsquare : 0 ≤ (t : ℝ)^2-9 := by nlinarith only [htR,sq_nonneg ((t : ℝ)-3)]
  have hh : 9*(L+Real.logb 2 (t : ℝ)) ≤ (t : ℝ)^2*(L+2) := by
    nlinarith only [hlog,hpoly,mul_nonneg hL hsquare]
  have hs : (3*Real.sqrt (L+Real.logb 2 (t : ℝ)))^2 ≤
      ((t : ℝ)*Real.sqrt (L+2))^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (add_nonneg hL he),
      Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+2)]
    norm_num only [show (3 : ℝ)^2 = 9 by norm_num]
    exact hh
  have hc := (sq_le_sq₀ (by positivity : 0 ≤ 3*Real.sqrt (L+Real.logb 2 (t : ℝ)))
    (by positivity : 0 ≤ (t : ℝ)*Real.sqrt (L+2))).mp hs
  nlinarith only [hc]

private theorem fourteen_le_quotient {x : ℝ} (hx : 32 ≤ x) :
    14 ≤ x/Real.sqrt (Real.logb 2 x) := by
  have h32 : Real.logb 2 (32 : ℝ) = 5 := by
    rw [show (32 : ℝ) = 2^5 by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  have hroot : Real.sqrt (5 : ℝ) ≤ 16/7 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hbase : (14 : ℝ) ≤ 32/Real.sqrt (Real.logb 2 (32 : ℝ)) := by
    rw [h32]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5))).mpr
    linarith only [hroot]
  exact hbase.trans (TraceyCoarseCeilingMonotonicity.quotient_mono (by norm_num) hx)

theorem eleven_generator_cost_le (r t : ℕ) (hr : 16 ≤ r) (hsmall : r < 32) (ht : 2 ≤ t)
    (H b : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 11) (hb0 : 0 ≤ b) (hb : b ≤ 1) :
    H+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  by_cases ht2 : t = 2
  · subst t
    have hrate : rate 2 = 1 := by
      norm_num [rate,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    have hceil : traceyPermutationGeneratorCeiling 2 = 2 := by
      norm_num [traceyPermutationGeneratorCeiling,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    have hh := fourteen_le_quotient (x := (r : ℝ)*2)
      (by
        have hr16 : (16 : ℝ) ≤ r := by exact_mod_cast hr
        linarith only [hr16])
    simp only [hrate,hceil,Nat.cast_ofNat,mul_one]
    linarith only [hH,hb,hh]
  let L := Real.logb 2 (r : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let w := Real.sqrt (L+e)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast (show 3 ≤ t by omega)
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r by omega))
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL he)
  have hLU : L ≤ 5 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 5 (by omega) (by decide)
      (by simpa only [pow_one] using (show r ≤ 2^5 by omega))
    simpa only [Nat.cast_one,div_one] using hh
  have hroot2 : Real.sqrt (L+2) ≤ 8/3 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [hLU]⟩
  have hroot4 : Real.sqrt (L+4) ≤ 3 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [hLU]⟩
  have hh2 := mul_le_mul hH hroot2 (Real.sqrt_nonneg (L+2)) (by norm_num : (0 : ℝ) ≤ 11)
  have hh4 := mul_le_mul (show b+2 ≤ 3 by linarith only [hb]) hroot4
    (Real.sqrt_nonneg (L+4)) (by norm_num : (0 : ℝ) ≤ 3)
  have hmargin : H/3*Real.sqrt (L+2)+(b+2)/2*Real.sqrt (L+4) ≤ (r : ℝ) := by
    have hr16 : (16 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith only [hh2,hh4,hr16]
  have hhead := mul_le_mul_of_nonneg_left (sqrt_log_add_le_third_mul L hL t (by omega)) hH0
  have htop := ImprimitiveMinimumRateScaling.ceiling_le_twice_rate t ht
  have hsource := mul_le_mul_of_nonneg_right htop (Real.sqrt_nonneg (L+e))
  have hrate := mul_le_mul_of_nonneg_left
    (ImprimitiveMinimumRateScaling.rate_mul_sqrt_log_add_le L hL t ht)
    (show 0 ≤ b+2 by linarith only [hb0])
  have hscaled := mul_le_mul_of_nonneg_left hmargin (show (0 : ℝ) ≤ t by positivity)
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change H+b*rate t+traceyPermutationGeneratorCeiling t ≤ (r : ℝ)*(t : ℝ)/w
  apply (le_div_iff₀ hw).mpr
  nlinarith only [hhead,hsource,hrate,hscaled]

end SymmetricSubgroupAsymptotics.NonaffineSmallUnitaryHeadOrdinaryAggregate
