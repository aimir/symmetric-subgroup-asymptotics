import SymmetricSubgroupAsymptotics.FusionPointingRatio

/-!
# An elementary hot-pointing denominator

The all-pairs monomial gives the needed benchmark lower bound directly.
No saddle estimate, logarithmic factorial estimate, or bound on the total
subgroup count enters this normalization.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

theorem criticalCoefficient_linear_lower (r : ℕ) :
    1 / ((2:ℚ)^r * (r.factorial:ℚ)) ≤ criticalCoefficient r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hc := criticalCoefficient_le_next r
    have hpos : 0 < (2:ℚ)*((r:ℚ)+1) := by positivity
    have hc' : criticalCoefficient r ≤ criticalCoefficient (r+1) * (2*((r:ℚ)+1)) := by
      simpa only [Nat.cast_add,Nat.cast_one,mul_comm,mul_left_comm,mul_assoc] using hc
    apply le_trans _ ((div_le_iff₀ hpos).mpr hc')
    apply (le_div_iff₀ hpos).mpr
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    convert ih using 1; field_simp

theorem parityCoefficient_linear_lower (n : ℕ) :
    1 / ((2:ℝ)^(halfDegree n) * ((halfDegree n).factorial:ℝ)) ≤
      (parityCoefficient n:ℝ) := by
  have hc : (criticalCoefficient (halfDegree n):ℝ) ≤ (parityCoefficient n:ℝ) := by
    have hq : criticalCoefficient (halfDegree n) ≤ parityCoefficient n := by
      unfold parityCoefficient
      split_ifs <;> linarith [criticalCoefficient_nonneg (halfDegree n-1)]
    exact_mod_cast hq
  apply le_trans _ hc
  have hh := (Rat.cast_le (K := ℝ)).mpr (criticalCoefficient_linear_lower (halfDegree n))
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
    Rat.cast_natCast] using hh

/-- Literal original factorial pointing before dividing by the action
normalizer. The large-complement hypothesis only ensures `r! ≤ b!`. -/
theorem fusionHot_pointing_denominator_le (b h : ℕ) (hwidth : 2*h≤b) :
    (((b+2*h).factorial:ℝ)/(b.factorial:ℝ)) / exactBenchmark (b+2*h) ≤
      eulerProduct⁻¹ * (2:ℝ)^(-((b+2*h:ℕ):ℝ)^2/16+
        5*((b+2*h:ℕ):ℝ)/8+1/4) := by
  let n := b+2*h
  let r := halfDegree n
  have hrb : r≤b := by dsimp [r,n,halfDegree]; omega
  have hrn : 2*r≤n := by dsimp [r,halfDegree]; omega
  have hnr : n≤2*r+1 := by dsimp [r,halfDegree]; omega
  have hφ := euler_positive
  have hc := parityCoefficient_linear_lower n
  have hG := fusionGaussianSum_lower r
  have hGpos : 0 < (binaryGaussianSum r:ℝ) := by exact_mod_cast binaryGaussianSum_pos r
  have hfac : (r.factorial:ℝ) ≤ (b.factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le hrb
  have hcoef : (2:ℝ)^(-(r:ℝ)) ≤ (b.factorial:ℝ)*(parityCoefficient n:ℝ) := by
    calc
      _ = (r.factorial:ℝ) * (1 / ((2:ℝ)^r*(r.factorial:ℝ))) := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
        field_simp
      _ ≤ (r.factorial:ℝ) * (parityCoefficient n:ℝ) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hfac (by
        exact_mod_cast (parityCoefficient_pos n).le)
  have hden : eulerProduct * (2:ℝ)^((r:ℝ)^2/4-(r:ℝ)-1/4) ≤
      (b.factorial:ℝ)*(binaryGaussianSum r:ℝ)*(parityCoefficient n:ℝ) := by
    calc
      _ = (eulerProduct*(2:ℝ)^((r:ℝ)^2/4-1/4)) * (2:ℝ)^(-(r:ℝ)) := by
        rw [mul_assoc,←Real.rpow_add (by norm_num : (0:ℝ)<2)]
        congr 2
        ring
      _ ≤ (binaryGaussianSum r:ℝ)*((b.factorial:ℝ)*(parityCoefficient n:ℝ)) :=
        mul_le_mul hG hcoef (by positivity) (by positivity)
      _ = _ := by ring
  have hexp : (n:ℝ)^2/16-5*(n:ℝ)/8-1/4 ≤ (r:ℝ)^2/4-(r:ℝ)-1/4 := by
    have hnrR : (n:ℝ)≤2*(r:ℝ)+1 := by exact_mod_cast hnr
    have hrnR : 2*(r:ℝ)≤(n:ℝ) := by exact_mod_cast hrn
    have hn0 : 0≤(n:ℝ) := by positivity
    have hr0 : 0≤(r:ℝ) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hnrR) (show 0≤(n:ℝ)+2*r by positivity)]
  have hden' : eulerProduct*(2:ℝ)^((n:ℝ)^2/16-5*(n:ℝ)/8-1/4) ≤
      (b.factorial:ℝ)*(binaryGaussianSum r:ℝ)*(parityCoefficient n:ℝ) :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hφ.le).trans hden
  calc
    _ = 1 / ((b.factorial:ℝ)*(binaryGaussianSum r:ℝ)*(parityCoefficient n:ℝ)) := by
      dsimp [exactBenchmark,n,r]
      field_simp
    _ ≤ 1 / (eulerProduct*(2:ℝ)^((n:ℝ)^2/16-5*(n:ℝ)/8-1/4)) :=
      one_div_le_one_div_of_le (by positivity) hden'
    _ = _ := by
      rw [one_div, mul_inv_rev, ←Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
      rw [mul_comm]
      dsimp [n]
      congr 2
      ring

end SymmetricSubgroupAsymptotics
