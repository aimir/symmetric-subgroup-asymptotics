import SymmetricSubgroupAsymptotics.NonaffineSmallDegreeOneHeadMargins
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity
import SymmetricSubgroupAsymptotics.ImprimitiveMinimumRateScaling

/-! The ONE strict-coset head in the actual local degree band32..127.
Three inherited top regimes retain the literal rounded coarse ceiling.
No pair-generation or model-specific group fact is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineSmallDegreeOneHeadOrdinaryAggregate
open ActualWreathChiefUnitMinimumRate

theorem one_factor_cost_le (r t ell : ℕ) (hr : 32 ≤ r) (hsmall : r < 128)
    (ht : 2 ≤ t) (hell : 2 ≤ ell) (hellr : ell ≤ r)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 3+Real.logb 2 (r : ℝ)) :
    (traceyPermutationGeneratorCeiling ell : ℝ)+b*rate t+traceyPermutationGeneratorCeiling t ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
  let L := Real.logb 2 (r : ℝ)
  let e := Real.logb 2 (t : ℝ)
  let v := Real.sqrt L
  let u1 := Real.sqrt (L+1)
  let u4 := Real.sqrt (L+4)
  let w := Real.sqrt (L+e)
  let H := (traceyPermutationGeneratorCeiling ell : ℝ)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL5 : 5 ≤ L := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower r 1 5 (by omega) (by decide)
      (by simpa only [pow_one] using hr)
    simpa only [Nat.cast_one,div_one] using hh
  have hL : 0 ≤ L := by linarith only [hL5]
  have he : 0 < e := Real.logb_pos (by norm_num) (by linarith only [htR])
  have hv : 0 < v := Real.sqrt_pos.mpr (by linarith only [hL5])
  have hw : 0 < w := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hL he)
  have hH : 0 ≤ H := by positivity
  obtain ⟨hmargin1,hmargin2,hmargin3⟩ := NonaffineSmallDegreeOneHeadMargins.margin_bounds r hr hsmall
  obtain ⟨hroot1,hroot4⟩ := NonaffineSmallDegreeOneHeadMargins.root_ratio_bounds L hL5
  have hhead : H ≤ (r : ℝ)/v+1 := by
    have hh : (traceyPermutationGeneratorCeiling r : ℝ) ≤ (r : ℝ)/v+1 := by
      change (⌈(r : ℝ)/v⌉₊ : ℝ) ≤ (r : ℝ)/v+1
      exact (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (r : ℝ)/v)).le
    have hm : H ≤ traceyPermutationGeneratorCeiling r := by
      change (traceyPermutationGeneratorCeiling ell : ℝ) ≤ (traceyPermutationGeneratorCeiling r : ℝ)
      exact_mod_cast TraceyCoarseCeilingMonotonicity.ceiling_mono hell hellr
    exact hm.trans hh
  have hquot1 : (r : ℝ)/v*u1 ≤ (11/10 : ℝ)*(r : ℝ) := by
    calc
      (r : ℝ)/v*u1 = (r : ℝ)*u1/v := by ring
      _ ≤ (r : ℝ)*((11/10 : ℝ)*v)/v :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot1 hrR.le) hv.le
      _ = (11/10 : ℝ)*(r : ℝ) := by rw [←mul_assoc,mul_div_cancel_right₀ _ hv.ne']; ring
  have hquot4 : (r : ℝ)/v*u4 ≤ (27/20 : ℝ)*(r : ℝ) := by
    calc
      (r : ℝ)/v*u4 = (r : ℝ)*u4/v := by ring
      _ ≤ (r : ℝ)*((27/20 : ℝ)*v)/v :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot4 hrR.le) hv.le
      _ = (27/20 : ℝ)*(r : ℝ) := by rw [←mul_assoc,mul_div_cancel_right₀ _ hv.ne']; ring
  have hhead1 := mul_le_mul_of_nonneg_right hhead (Real.sqrt_nonneg (L+1))
  have hhead4 := mul_le_mul_of_nonneg_right hhead (Real.sqrt_nonneg (L+4))
  have hb4 := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (L+4))
  have hscaled : (H+b*rate t+traceyPermutationGeneratorCeiling t)*w ≤ (r : ℝ)*(t : ℝ) := by
    by_cases htwo : t = 2
    · subst t
      have hrate : rate 2 = 1 := by
        norm_num [rate,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      have hceil : traceyPermutationGeneratorCeiling 2 = 2 := by
        norm_num [traceyPermutationGeneratorCeiling,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      have hw1 : w = u1 := by
        dsimp only [w,e,u1]
        norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      rw [hrate,hceil,hw1]
      norm_num only [Nat.cast_ofNat,mul_one]
      have hb1 := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (L+1))
      nlinarith only [hhead1,hquot1,hb1,hmargin1]
    · by_cases hlarge : 16 ≤ t
      · have he4 : 4 ≤ e := by
          have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 4 (by omega) (by decide)
            (by simpa only [pow_one] using hlarge)
          simpa only [Nat.cast_one,div_one] using hh
        let ve := Real.sqrt e
        have hve : 0 < ve := Real.sqrt_pos.mpr he
        have heUpper : e ≤ (t : ℝ)-1 :=
          BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one t ht
        have ht16 : (16 : ℝ) ≤ t := by exact_mod_cast hlarge
        have htSq : 16 ≤ (t : ℝ)^2 := by nlinarith only [ht16]
        have hLmul := mul_nonneg (show 0 ≤ (t : ℝ)^2-16 by linarith only [htSq]) hL
        have htscale := mul_le_mul_of_nonneg_right ht16 (show (0 : ℝ) ≤ t by positivity)
        have hheadW : w ≤ (t : ℝ)/4*u1 := by
          apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
          dsimp only [w,u1]
          rw [mul_pow,Real.sq_sqrt (add_nonneg hL he.le),Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+1)]
          nlinarith only [heUpper,hLmul,htscale]
        have hprod : w ≤ u4*ve/2 := by
          have hh : (2*w)^2 ≤ (u4*ve)^2 := by
            dsimp only [w,u4,ve]
            rw [mul_pow,mul_pow,Real.sq_sqrt (add_nonneg hL he.le),
              Real.sq_sqrt (by linarith only [hL] : 0 ≤ L+4),Real.sq_sqrt he.le]
            nlinarith only [mul_nonneg hL (show 0 ≤ e-4 by linarith only [he4])]
          have hh' := (sq_le_sq₀ (by positivity) (by positivity)).mp hh
          linarith only [hh']
        have hlogScaled : (t : ℝ)/ve*w ≤ (t : ℝ)/2*u4 := by
          calc
            (t : ℝ)/ve*w = (t : ℝ)*w/ve := by ring
            _ ≤ (t : ℝ)*(u4*ve/2)/ve :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity)) hve.le
            _ = (t : ℝ)/2*u4 := by
              calc
                (t : ℝ)*(u4*ve/2)/ve = (((t : ℝ)/2*u4)*ve)/ve := by ring
                _ = (t : ℝ)/2*u4 := mul_div_cancel_right₀ _ hve.ne'
        have htop : (traceyPermutationGeneratorCeiling t : ℝ) ≤ (t : ℝ)/ve+1 := by
          change (⌈(t : ℝ)/ve⌉₊ : ℝ) ≤ (t : ℝ)/ve+1
          exact (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (t : ℝ)/ve)).le
        have hrate : rate t ≤ (t : ℝ)/ve := min_le_right _ _
        have hcost : H+b*rate t+traceyPermutationGeneratorCeiling t ≤ H+1+(b+1)*((t : ℝ)/ve) := by
          have hh := mul_le_mul_of_nonneg_left hrate hb0
          nlinarith only [hh,htop]
        have hnormal : (H+1)/4*u1+(b+1)/2*u4 ≤ (r : ℝ) := by
          nlinarith only [hhead1,hquot1,hb4,hmargin3]
        have hsource := mul_le_mul_of_nonneg_right hcost hw.le
        have hh := mul_le_mul_of_nonneg_left hheadW (show 0 ≤ H+1 by linarith only [hH])
        have hh' := mul_le_mul_of_nonneg_left hlogScaled (show 0 ≤ b+1 by linarith only [hb0])
        have hn := mul_le_mul_of_nonneg_left hnormal (show (0 : ℝ) ≤ t by positivity)
        nlinarith only [hsource,hh,hh',hn]
      · have ht3 : 3 ≤ t := by omega
        have he4 : e ≤ 4 := by
          have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 4 (by omega) (by decide)
            (by simpa only [pow_one] using (show t ≤ 2^4 by omega))
          simpa only [Nat.cast_one,div_one] using hh
        have hwu : w ≤ u4 := Real.sqrt_le_sqrt (add_le_add (le_refl L) he4)
        have hrate : rate t ≤ (t : ℝ)/2 := min_le_left _ _
        have htop : (traceyPermutationGeneratorCeiling t : ℝ) ≤ t := by
          have hh := ImprimitiveMinimumRateScaling.ceiling_le_twice_rate t ht
          nlinarith only [hh,hrate]
        have hcost : H+b*rate t+traceyPermutationGeneratorCeiling t ≤ H+(b+2)*(t : ℝ)/2 := by
          have hh := mul_le_mul_of_nonneg_left hrate hb0
          nlinarith only [hh,htop]
        have hratenonneg : 0 ≤ rate t := (one_le_rate t ht).trans' (by norm_num)
        have hcost0 : 0 ≤ H+b*rate t+traceyPermutationGeneratorCeiling t := by positivity
        have hsource := mul_le_mul_of_nonneg_left hwu hcost0
        have hcostU := mul_le_mul_of_nonneg_right hcost (Real.sqrt_nonneg (L+4))
        have hHtop := mul_le_mul_of_nonneg_right (show (3 : ℝ) ≤ t by exact_mod_cast ht3)
          (show 0 ≤ H*u4 by positivity)
        have hnormal : H/3*u4+(b+2)/2*u4 ≤ (r : ℝ) := by
          nlinarith only [hhead4,hquot4,hb4,hmargin2]
        have hn := mul_le_mul_of_nonneg_left hnormal (show (0 : ℝ) ≤ t by positivity)
        nlinarith only [hsource,hcostU,hHtop,hn]
  rw [Real.logb_mul hrR.ne' (by linarith only [htR] : (t : ℝ) ≠ 0)]
  change H+b*rate t+traceyPermutationGeneratorCeiling t ≤ (r : ℝ)*(t : ℝ)/w
  exact (le_div_iff₀ hw).mpr hscaled

end SymmetricSubgroupAsymptotics.NonaffineSmallDegreeOneHeadOrdinaryAggregate
