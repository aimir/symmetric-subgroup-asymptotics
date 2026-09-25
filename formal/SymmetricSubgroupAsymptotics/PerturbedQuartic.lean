import SymmetricSubgroupAsymptotics.CriticalProfiles
import SymmetricSubgroupAsymptotics.ShiftedCoefficientRatio

/-!
# Exponential loss in the actual exceptional profile sum

The original four-colour weights are multiplied by the proved product gap.
Their perturbed exponential majorant has half the quartic coefficient. The
original saddle lower bound then gives a uniform positive exponential loss.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- The actual weighted profile sum, retaining each original colour. -/
def perturbedProfileCoefficient (r : ℕ) : ℝ :=
  ∑ p ∈ criticalProfiles r, (p.weight : ℝ) *
    (2 : ℝ)^(-((p.c2 : ℝ)/2 + p.v4 + p.e8))

/-- The positive perturbed polynomial, with the two rank-two colours
combined by `1/48 + 1/8 = 7/48`. -/
def perturbedCriticalPolynomial (x : ℝ) : ℝ :=
  x / (2 * Real.sqrt 2) + 7*x^2/48 + x^4/768

theorem perturbedProfileCoefficient_nonneg (r : ℕ) : 0 ≤ perturbedProfileCoefficient r := by
  apply Finset.sum_nonneg
  intro p hp
  unfold CriticalProfile.weight
  positivity

private theorem profile_gap_factor (p : CriticalProfile) :
    (2 : ℝ)^(-((p.c2 : ℝ)/2 + p.v4 + p.e8)) =
      (Real.sqrt 2)⁻¹ ^ p.c2 * (2 : ℝ)⁻¹ ^ p.v4 * (2 : ℝ)⁻¹ ^ p.e8 := by
  rw [show -((p.c2 : ℝ)/2 + p.v4 + p.e8) =
    (-1/2 : ℝ)*p.c2 + (-(p.v4 : ℝ)) + (-(p.e8 : ℝ)) by ring]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [Real.rpow_natCast,inv_pow]
  congr 2
  rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),← Real.sqrt_eq_rpow]
  simp only [inv_pow]

private def perturbedProfileTerm (x : ℝ) (p : CriticalProfile) : ℝ :=
  ((x/(2*Real.sqrt 2))^p.c2 / (p.c2.factorial : ℝ)) *
    ((x^2/48)^p.v4 / (p.v4.factorial : ℝ)) *
    ((x^2/8)^p.d8 / (p.d8.factorial : ℝ)) *
    ((x^4/768)^p.e8 / (p.e8.factorial : ℝ))

private theorem perturbedProfileTerm_nonneg {x : ℝ} (hx : 0 ≤ x) (p : CriticalProfile) :
    0 ≤ perturbedProfileTerm x p := by unfold perturbedProfileTerm; positivity

private theorem perturbedProfileTerm_eq (x : ℝ) (p : CriticalProfile) :
    (p.weight : ℝ) * (2 : ℝ)^(-((p.c2 : ℝ)/2 + p.v4 + p.e8)) * x^p.rank =
      perturbedProfileTerm x p := by
  rw [profile_gap_factor]
  unfold CriticalProfile.weight CriticalProfile.rank perturbedProfileTerm
  push_cast
  simp only [pow_add,pow_mul,div_pow,mul_pow,inv_pow]
  have h48 : (48 : ℝ)^p.v4 = 24^p.v4 * 2^p.v4 := by rw [← mul_pow]; norm_num
  have h768 : (768 : ℝ)^p.e8 = 384^p.e8 * 2^p.e8 := by rw [← mul_pow]; norm_num
  rw [h48,h768]
  field_simp

private abbrev ProfileBoxIndex := (ℕ × ℕ) × (ℕ × ℕ)

private def profileBox (r : ℕ) : Finset ProfileBoxIndex :=
  ((Finset.range (r+1)).product (Finset.range (r+1))).product
    ((Finset.range (r+1)).product (Finset.range (r+1)))

private def profileBoxValue (p : ProfileBoxIndex) : CriticalProfile :=
  ⟨p.1.1,p.1.2,p.2.1,p.2.2⟩

private theorem profileBoxValue_injective : Function.Injective profileBoxValue := by
  rintro ⟨⟨a,v⟩,b,d⟩ ⟨⟨a',v'⟩,b',d'⟩ h
  have ha := congrArg CriticalProfile.c2 h
  have hv := congrArg CriticalProfile.v4 h
  have hb := congrArg CriticalProfile.d8 h
  have hd := congrArg CriticalProfile.e8 h
  simpa [profileBoxValue,Prod.ext_iff] using And.intro (And.intro ha hv) (And.intro hb hd)

private theorem criticalProfiles_subset_box (r : ℕ) :
    criticalProfiles r ⊆ (profileBox r).image profileBoxValue := by
  intro p hp
  have hr := (mem_criticalProfiles r p).mp hp
  refine Finset.mem_image.mpr ⟨((p.c2,p.v4),(p.d8,p.e8)),?_,rfl⟩
  simp only [profileBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range]
  unfold CriticalProfile.rank at hr
  omega

/-- The actual weighted profile sum has the positive perturbed-polynomial
majorant at every nonnegative radius. No coefficient identity is assumed. -/
theorem perturbedProfileCoefficient_mul_pow_le_exp (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    perturbedProfileCoefficient r * x^r ≤ Real.exp (perturbedCriticalPolynomial x) := by
  have he : perturbedProfileCoefficient r * x^r =
      ∑ p ∈ criticalProfiles r, perturbedProfileTerm x p := by
    unfold perturbedProfileCoefficient
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← (mem_criticalProfiles r p).mp hp]
    exact perturbedProfileTerm_eq x p
  rw [he]
  calc
    _ ≤ ∑ p ∈ (profileBox r).image profileBoxValue, perturbedProfileTerm x p :=
      Finset.sum_le_sum_of_subset_of_nonneg (criticalProfiles_subset_box r)
        (fun p _ _ ↦ perturbedProfileTerm_nonneg hx p)
    _ = (∑ a ∈ Finset.range (r+1), (x/(2*Real.sqrt 2))^a / (a.factorial : ℝ)) *
        (∑ v ∈ Finset.range (r+1), (x^2/48)^v / (v.factorial : ℝ)) *
        (∑ b ∈ Finset.range (r+1), (x^2/8)^b / (b.factorial : ℝ)) *
        (∑ d ∈ Finset.range (r+1), (x^4/768)^d / (d.factorial : ℝ)) := by
      rw [Finset.sum_image profileBoxValue_injective.injOn]
      simp only [profileBox,Finset.product_eq_sprod,Finset.sum_product,profileBoxValue,perturbedProfileTerm]
      simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
    _ ≤ Real.exp (x/(2*Real.sqrt 2)) * Real.exp (x^2/48) *
        Real.exp (x^2/8) * Real.exp (x^4/768) := by
      gcongr
      · exact Real.sum_le_exp_of_nonneg (by positivity) _
      · exact Real.sum_le_exp_of_nonneg (by positivity) _
      · exact Real.sum_le_exp_of_nonneg (by positivity) _
      · exact Real.sum_le_exp_of_nonneg (by positivity) _
    _ = _ := by
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
      congr 1
      unfold perturbedCriticalPolynomial
      ring

/-- The perturbed quartic loses a definite part of the original positive
exponent; the smaller linear and quadratic coefficients only improve it. -/
theorem perturbedCriticalPolynomial_le {x : ℝ} (hx : 0 ≤ x) :
    perturbedCriticalPolynomial x ≤ criticalPolynomial x - x^4/768 := by
  have hs : 1 ≤ Real.sqrt (2 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have hlin : x/(2*Real.sqrt 2) ≤ x/2 :=
    div_le_div_of_nonneg_left hx (by norm_num) (by nlinarith)
  unfold perturbedCriticalPolynomial criticalPolynomial
  nlinarith [sq_nonneg x]

/-- An explicit large-rank quartic mass bound at the original saddle. -/
theorem saddleRadius_quartic_mass_lower (r : ℕ) (hr : 69 ≤ r) :
    48*(r : ℝ) ≤ saddleRadius r^4 := by
  have hr0 : 0 < r := by omega
  have hρ := (saddleRadius_pos r hr0).le
  have h8 : (8 : ℝ) ≤ saddleRadius r := by
    by_contra h
    have hmean := saddleMean_strictMonoOn.monotoneOn hρ (by norm_num : (0 : ℝ) ≤ 8)
      (le_of_lt (lt_of_not_ge h))
    rw [saddleMean_saddleRadius r hr0] at hmean
    have hr' : (69 : ℝ) ≤ r := by exact_mod_cast hr
    norm_num [saddleMean] at hmean
    linarith
  have hsq : (64 : ℝ) ≤ saddleRadius r^2 := by nlinarith
  have h4 : 64*saddleRadius r^2 ≤ saddleRadius r^4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (saddleRadius r))]
  have hlin : 48*saddleRadius r ≤ 6*saddleRadius r^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h8) hρ]
  have he := saddleRadius_quartic r hr0
  rw [saddleScale_pow_four] at he
  nlinarith

private theorem original_saddle_eventual_lower :
    ∃ N : ℕ, 69 ≤ N ∧ ∀ r : ℕ, N ≤ r →
      Real.exp (criticalPolynomial (saddleRadius r)) ≤
        2*(criticalCoefficient r : ℝ)*saddleRadius r^r *
          Real.sqrt (2*Real.pi*saddleVariance (saddleRadius r)) := by
  obtain ⟨C,hC,N,hN,h⟩ := normalizedSaddleIntegral_rank_error
  obtain ⟨M,hM⟩ := exists_nat_gt (2*C)
  refine ⟨max 69 (max N M),le_max_left _ _,?_⟩
  intro r hr
  have hr0 : 0 < r := by omega
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hrN : N ≤ r := by omega
  have hrM : M ≤ r := by omega
  have hMr : (M : ℝ) ≤ r := by exact_mod_cast hrM
  have hhalf : C/(r : ℝ) ≤ 1/2 := (div_le_iff₀ hr').mpr (by linarith)
  have hI := h r hrN 0 (by norm_num) (by norm_num)
  have hl : (1/2 : ℝ) ≤ normalizedSaddleIntegral (saddleRadius r) 0 := by
    have := (abs_le.mp hI).1
    linarith
  rw [criticalCoefficient_normalizedSaddleIntegral_zero r hr0] at hl
  have hm := (le_div_iff₀ (Real.exp_pos _)).mp hl
  nlinarith

/-- Before absorbing the polynomial prefactor, the actual weighted profile
ratio already has a uniform real exponential loss. -/
theorem perturbedProfileCoefficient_ratio_exp_bound :
    ∃ N : ℕ, 69 ≤ N ∧ ∀ r : ℕ, N ≤ r →
      perturbedProfileCoefficient r / (criticalCoefficient r : ℝ) ≤
        8*Real.pi*Real.sqrt (r : ℝ)*Real.exp (-(r : ℝ)/16) := by
  obtain ⟨N,hN,hn⟩ := original_saddle_eventual_lower
  refine ⟨N,hN,?_⟩
  intro r hr
  have hr69 : 69 ≤ r := hN.trans hr
  have hr0 : 0 < r := by omega
  have hρ := saddleRadius_pos r hr0
  have hc : (0 : ℝ) < criticalCoefficient r := by exact_mod_cast criticalCoefficient_pos r
  have hpower : (0 : ℝ) < saddleRadius r^r := pow_pos hρ r
  have hpoly : perturbedCriticalPolynomial (saddleRadius r) ≤
      criticalPolynomial (saddleRadius r) - (r : ℝ)/16 := by
    have hp := perturbedCriticalPolynomial_le hρ.le
    have hquartic := saddleRadius_quartic_mass_lower r hr69
    linarith
  have hnum : perturbedProfileCoefficient r * saddleRadius r^r ≤
      (2*(criticalCoefficient r : ℝ)*saddleRadius r^r *
        Real.sqrt (2*Real.pi*saddleVariance (saddleRadius r))) * Real.exp (-(r : ℝ)/16) := by
    calc
      _ ≤ Real.exp (perturbedCriticalPolynomial (saddleRadius r)) :=
        perturbedProfileCoefficient_mul_pow_le_exp r hρ.le
      _ ≤ Real.exp (criticalPolynomial (saddleRadius r) - (r : ℝ)/16) := Real.exp_le_exp.mpr hpoly
      _ = Real.exp (criticalPolynomial (saddleRadius r)) * Real.exp (-(r : ℝ)/16) :=
        by simp only [sub_eq_add_neg,Real.exp_add,neg_div]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hn r hr) (Real.exp_pos _).le
  have hs : Real.sqrt (2*Real.pi*saddleVariance (saddleRadius r)) ≤
      4*Real.pi*Real.sqrt (r : ℝ) := by
    have hb := (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mp (saddle_normalizer_bound r hr0)
    nlinarith
  apply (div_le_iff₀ hc).mpr
  apply (mul_le_mul_iff_left₀ hpower).mp
  calc
    _ ≤ (2*(criticalCoefficient r : ℝ)*saddleRadius r^r *
        Real.sqrt (2*Real.pi*saddleVariance (saddleRadius r))) * Real.exp (-(r : ℝ)/16) := hnum
    _ ≤ (2*(criticalCoefficient r : ℝ)*saddleRadius r^r *
        (4*Real.pi*Real.sqrt (r : ℝ))) * Real.exp (-(r : ℝ)/16) := by gcongr
    _ = _ := by ring

private theorem sqrt_mul_exp_bound {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x * Real.exp (-x/16) ≤ 32*Real.exp (-x/32) := by
  have hs : Real.sqrt x ≤ x+1 := by
    have hsq := Real.sq_sqrt hx
    have hnon := Real.sqrt_nonneg x
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have he := Real.add_one_le_exp (x/32)
  have h32 : Real.sqrt x ≤ 32*Real.exp (x/32) := by linarith
  calc
    _ ≤ (32*Real.exp (x/32))*Real.exp (-x/16) :=
      mul_le_mul_of_nonneg_right h32 (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring

private theorem exp_negative_le_two_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x/32) ≤ (2 : ℝ)^(-x/32) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hl : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- A fixed exponential loss for the actual exceptional profile weights.
The rate is explicit; only the cutoff inherits the original saddle estimate. -/
theorem perturbedProfileCoefficient_ratio_exponential :
    ∃ N : ℕ, 69 ≤ N ∧ ∀ r : ℕ, N ≤ r →
      perturbedProfileCoefficient r / (criticalCoefficient r : ℝ) ≤
        (256*Real.pi)*(2 : ℝ)^(-(r : ℝ)/32) := by
  obtain ⟨N,hN,hn⟩ := perturbedProfileCoefficient_ratio_exp_bound
  refine ⟨N,hN,?_⟩
  intro r hr
  calc
    _ ≤ 8*Real.pi*Real.sqrt (r : ℝ)*Real.exp (-(r : ℝ)/16) := hn r hr
    _ = (8*Real.pi)*(Real.sqrt (r : ℝ)*Real.exp (-(r : ℝ)/16)) := by ring
    _ ≤ (8*Real.pi)*(32*Real.exp (-(r : ℝ)/32)) := by
      exact mul_le_mul_of_nonneg_left (sqrt_mul_exp_bound (by positivity : (0 : ℝ) ≤ r))
        (by positivity)
    _ ≤ (8*Real.pi)*(32*(2 : ℝ)^(-(r : ℝ)/32)) := by
      gcongr
      exact exp_negative_le_two_rpow (by positivity)
    _ = _ := by ring

/-- Existential-rate interface for downstream weighted profile assembly. -/
theorem perturbedProfileCoefficient_ratio_exponential_uniform :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      perturbedProfileCoefficient r / (criticalCoefficient r : ℝ) ≤
        C*(2 : ℝ)^(-c*(r : ℝ)) := by
  obtain ⟨N,hN,hn⟩ := perturbedProfileCoefficient_ratio_exponential
  refine ⟨1/32,256*Real.pi,by norm_num,by positivity,N,?_⟩
  intro r hr
  rw [show -(1/32 : ℝ)*(r : ℝ) = -(r : ℝ)/32 by ring]
  exact hn r hr

end SymmetricSubgroupAsymptotics
