import SymmetricSubgroupAsymptotics.FusionCold
import SymmetricSubgroupAsymptotics.FusionShiftedMenu

/-!
# Original benchmark normalization for arbitrary deleted widths

An odd deletion changes the parity coefficient and may increase Gaussian
rank by either floor(w/2) or ceil(w/2). The uniform linear pointing loss is
therefore floor(w/2)*b/4. The guarded parity coefficient is retained exactly.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

theorem analyticParityCoefficient_lower (ε k : ℕ) :
    criticalCoefficient k ≤ analyticParityCoefficient ε k := by
  unfold analyticParityCoefficient
  split_ifs <;> linarith [criticalCoefficient_nonneg (k-1)]

theorem analyticParityCoefficient_upper (ε k : ℕ) :
    analyticParityCoefficient ε k ≤ ((k:ℚ)+1)*criticalCoefficient k := by
  unfold analyticParityCoefficient
  split_ifs with hk
  · have hs := criticalCoefficient_shift_le k 1 hk.2
    norm_num at hs
    nlinarith [criticalCoefficient_nonneg k,
      mul_nonneg (show 0≤(k:ℚ) by positivity) (criticalCoefficient_nonneg k)]
  · nlinarith [mul_nonneg (show 0≤(k:ℚ) by positivity) (criticalCoefficient_nonneg k)]

theorem analyticParityCoefficient_cross_shift (ε δ k t : ℕ) :
    analyticParityCoefficient ε k ≤
      ((k:ℚ)+1)*(2*((k+t:ℕ):ℚ))^t * analyticParityCoefficient δ (k+t) := by
  have hs := criticalCoefficient_shift_le (k+t) t (by omega)
  simp only [Nat.add_sub_cancel] at hs
  calc
    _ ≤ ((k:ℚ)+1)*criticalCoefficient k := analyticParityCoefficient_upper ε k
    _ ≤ ((k:ℚ)+1)*((2*((k+t:ℕ):ℚ))^t * criticalCoefficient (k+t)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (analyticParityCoefficient_lower δ (k+t))
        (by positivity)

/-- Exact original factorial ratio, with no parity restriction on the width. -/
def fusionWidthPointingRatio (b w : ℕ) : ℝ :=
  ((b+w).factorial:ℝ)/(b.factorial:ℝ)*exactBenchmark b/exactBenchmark (b+w)

theorem fusionWidthPointingRatio_nonneg (b w : ℕ) :
    0 ≤ fusionWidthPointingRatio b w := by
  unfold fusionWidthPointingRatio
  have hb := exactBenchmark_pos b
  have hn := exactBenchmark_pos (b+w)
  positivity

theorem fusionWidthPointingRatio_even (b h : ℕ) :
    fusionWidthPointingRatio b (2*h) = fusionPointingRatio b h := rfl

theorem fusionWidthPointingRatio_eq (b w : ℕ) :
    fusionWidthPointingRatio b w =
      ((binaryGaussianSum (halfDegree b):ℝ)/binaryGaussianSum (halfDegree (b+w))) *
      ((analyticParityCoefficient (parity b) (halfDegree b):ℝ)/
        analyticParityCoefficient (parity (b+w)) (halfDegree (b+w))) := by
  unfold fusionWidthPointingRatio exactBenchmark
  rw [← analyticParityCoefficient_halfDegree b,
    ← analyticParityCoefficient_halfDegree (b+w)]
  have hf : (b.factorial:ℝ) ≠ 0 := by positivity
  have hF : ((b+w).factorial:ℝ) ≠ 0 := by positivity
  field_simp

/-- Uniform in both parities, including odd deletion and rank zero. -/
theorem fusionWidthPointingRatio_le (b w : ℕ) :
    fusionWidthPointingRatio b w ≤
      (eulerProduct⁻¹^2 * (2:ℝ)^(((w:ℝ)+1)/4)) *
      ((b+w+1:ℕ):ℝ)^(w+2) * (2:ℝ)^(-(halfDegree w:ℝ)*b/4) := by
  let k := halfDegree b
  let t := halfDegree (b+w)-k
  have hkt : k+t = halfDegree (b+w) := by dsimp [k,t,halfDegree]; omega
  have htw : t≤w := by dsimp [t,k,halfDegree]; omega
  have hht : halfDegree w≤t := by dsimp [t,k,halfDegree]; omega
  have hkb : b≤2*k+1 := by dsimp [k,halfDegree]; omega
  have hkn : 2*(k+t)≤b+w := by rw [hkt]; unfold halfDegree; omega
  have hφ := euler_positive
  have hcoefpos : 0 < (analyticParityCoefficient (parity (b+w)) (k+t):ℝ) := by
    exact_mod_cast analyticParityCoefficient_positive (parity (b+w)) (k+t)
  have hcoef : (analyticParityCoefficient (parity b) k:ℝ)/
      analyticParityCoefficient (parity (b+w)) (k+t) ≤
      ((k:ℝ)+1)*(2*((k+t:ℕ):ℝ))^t := by
    apply (div_le_iff₀ hcoefpos).mpr
    exact_mod_cast analyticParityCoefficient_cross_shift (parity b) (parity (b+w)) k t
  have hpoly : ((k:ℝ)+1)^2 * (2*((k+t:ℕ):ℝ))^t ≤
      ((b+w+1:ℕ):ℝ)^(w+2) := by
    have hk : (k:ℝ)+1≤((b+w+1:ℕ):ℝ) := by exact_mod_cast (show k+1≤b+w+1 by omega)
    have hn : 2*((k+t:ℕ):ℝ)≤((b+w+1:ℕ):ℝ) := by
      exact_mod_cast (show 2*(k+t)≤b+w+1 by omega)
    have h1 : (1:ℝ)≤((b+w+1:ℕ):ℝ) := by exact_mod_cast (show 1≤b+w+1 by omega)
    calc
      _ ≤ ((b+w+1:ℕ):ℝ)^2 * ((b+w+1:ℕ):ℝ)^t :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hk 2)
          (pow_le_pow_left₀ (by positivity) hn t) (by positivity) (by positivity)
      _ = ((b+w+1:ℕ):ℝ)^(t+2) := by rw [←pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ h1 (by omega)
  have hexp : -(t:ℝ)*k/2-(t:ℝ)^2/4+1/4 ≤
      ((w:ℝ)+1)/4 + (-(halfDegree w:ℝ)*b/4) := by
    have hhtR : (halfDegree w:ℝ)≤(t:ℝ) := by exact_mod_cast hht
    have hhwR : (halfDegree w:ℝ)≤(w:ℝ) := by
      exact_mod_cast (show halfDegree w≤w by unfold halfDegree; omega)
    have hkbR : (b:ℝ)≤2*(k:ℝ)+1 := by exact_mod_cast hkb
    nlinarith [sq_nonneg (t:ℝ),
      mul_nonneg (sub_nonneg.mpr hhtR) (show 0≤(k:ℝ) by positivity),
      mul_nonneg (show 0≤(halfDegree w:ℝ) by positivity) (sub_nonneg.mpr hkbR)]
  rw [fusionWidthPointingRatio_eq, ←hkt]
  change ((binaryGaussianSum k:ℝ)/binaryGaussianSum (k+t)) *
    ((analyticParityCoefficient (parity b) k:ℝ)/
      analyticParityCoefficient (parity (b+w)) (k+t)) ≤ _
  calc
    _ ≤ (eulerProduct⁻¹^2*((k:ℝ)+1)*(2:ℝ)^(-(t:ℝ)*k/2-(t:ℝ)^2/4+1/4)) *
        (((k:ℝ)+1)*(2*((k+t:ℕ):ℝ))^t) := by
      apply mul_le_mul (fusionGaussianRatio_le k t) hcoef
      · exact div_nonneg (by exact_mod_cast (analyticParityCoefficient_positive _ _).le)
          hcoefpos.le
      · positivity
    _ = eulerProduct⁻¹^2 * (((k:ℝ)+1)^2*(2*((k+t:ℕ):ℝ))^t) *
        (2:ℝ)^(-(t:ℝ)*k/2-(t:ℝ)^2/4+1/4) := by ring
    _ ≤ eulerProduct⁻¹^2 * ((b+w+1:ℕ):ℝ)^(w+2) *
        (2:ℝ)^(((w:ℝ)+1)/4 + (-(halfDegree w:ℝ)*b/4)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity))
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity) (by positivity)
    _ = _ := by rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]; ring

/-- Original divisor and actual local exponential envelope, at arbitrary width. -/
def fusionWidthColdKernel (b w : ℕ) (D a α : ℝ) : ℝ :=
  fusionWidthPointingRatio b w * (D/a) * (2:ℝ)^(α*b)

theorem fusionWidthColdKernel_nonneg (b w : ℕ) {D a α : ℝ}
    (hD : 0≤D) (ha : 0<a) : 0≤fusionWidthColdKernel b w D a α := by
  unfold fusionWidthColdKernel
  exact mul_nonneg (mul_nonneg (fusionWidthPointingRatio_nonneg b w)
    (div_nonneg hD ha.le)) (by positivity)

/-- The capacity threshold uses floor(w/2), including for odd deletions.
No bound on normalized total subgroup counts is assumed. -/
theorem fusionWidthColdKernel_eventually (w : ℕ) {D a α : ℝ}
    (hD : 0≤D) (ha : 0<a) (hgap : α<(halfDegree w:ℝ)/4) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ b : ℕ in atTop,
      fusionWidthColdKernel b w D a α ≤
        C*(2:ℝ)^(-(((halfDegree w:ℝ)/4-α)/2)*b) := by
  let δ : ℝ := (halfDegree w:ℝ)/4-α
  let A : ℝ := eulerProduct⁻¹^2 * (2:ℝ)^(((w:ℝ)+1)/4)*(D/a)
  have hδ : 0<δ := sub_pos.mpr hgap
  have hφ := euler_positive
  have hA : 0≤A := by dsimp [A]; positivity
  have hbound (b : ℕ) : fusionWidthColdKernel b w D a α ≤
      A*((b+w+1:ℕ):ℝ)^(w+2)*(2:ℝ)^(-δ*b) := by
    unfold fusionWidthColdKernel
    calc
      _ ≤ ((eulerProduct⁻¹^2*(2:ℝ)^(((w:ℝ)+1)/4))*
          ((b+w+1:ℕ):ℝ)^(w+2)*(2:ℝ)^(-(halfDegree w:ℝ)*b/4)) *
          (D/a)*(2:ℝ)^(α*b) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (fusionWidthPointingRatio_le b w)
            (div_nonneg hD ha.le)) (by positivity)
      _ = _ := by
        have he : -δ*b = -(halfDegree w:ℝ)*b/4+α*b := by dsimp [δ]; ring
        rw [he, Real.rpow_add (by norm_num : (0:ℝ)<2)]
        dsimp [A]
        ring
  refine ⟨A*((w+2:ℕ):ℝ)^(w+2)+1, by positivity, ?_⟩
  filter_upwards [eventually_shifted_natpow_mul_exponential_le (w+1) (w+2) hδ] with b hb
  have hs : b+(w+1)=b+w+1 := by omega
  rw [hs] at hb
  calc
    _ ≤ A*(((b+w+1:ℕ):ℝ)^(w+2)*(2:ℝ)^(-δ*b)) := by
      simpa only [mul_assoc] using hbound b
    _ ≤ A*(((w+2:ℕ):ℝ)^(w+2)*(2:ℝ)^(-(δ/2)*b)) :=
      mul_le_mul_of_nonneg_left hb hA
    _ ≤ _ := by
      dsimp [δ]
      nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2)
        (-(((halfDegree w:ℝ)/4-α)/2)*b)]

/-- Fixed finite menus may mix odd and even removed widths. -/
theorem fusionWidthColdKernel_shifted_sum {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (D a α : ι → ℝ)
    (hD : ∀ i, 0≤D i) (ha : ∀ i, 0<a i)
    (hgap : ∀ i, α i<(halfDegree (w i):ℝ)/4) :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      (∑ i, fusionWidthColdKernel (n-w i) (w i) (D i) (a i) (α i)) ≤
        C*(2:ℝ)^(-κ*(n:ℝ)) := by
  have h := fusion_finite_shifted_decay
    (fun i b => fusionWidthColdKernel b (w i) (D i) (a i) (α i)) w 1 (fun i => ?_)
  · simpa using h
  · obtain ⟨C,hC,hb⟩ := fusionWidthColdKernel_eventually (w i) (hD i) (ha i) (hgap i)
    exact ⟨C, ((halfDegree (w i):ℝ)/4-α i)/2, hC,
      div_pos (sub_pos.mpr (hgap i)) (by norm_num), by simpa using hb⟩

end SymmetricSubgroupAsymptotics
