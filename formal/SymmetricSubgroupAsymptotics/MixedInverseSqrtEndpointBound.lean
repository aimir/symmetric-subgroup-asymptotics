import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A shared endpoint principle for the inverse-rate square-root envelopes
appearing after characteristic divisor weights. Squaring gives a positive
linear combination of x^-2, x^-1, a constant and x. Convexity retains the
whole interval; no grid, cutoff, group or asymptotic premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MixedInverseSqrtEndpointBound

def mixed (a b c k x : ℝ) : ℝ := (a/x+b)*Real.sqrt (c+k*x)

private def expanded (a b c k x : ℝ) : ℝ :=
  a^2*c*x^(-2 : ℤ) + (a^2*k+2*a*b*c)*x^(-1 : ℤ) +
    (2*a*b*k+b^2*c) + b^2*k*x

private theorem square_expansion (a b c k x : ℝ) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hx : 0 < x) : (mixed a b c k x)^2 = expanded a b c k x := by
  have hrad : 0 ≤ c+k*x := add_nonneg hc (mul_nonneg hk hx.le)
  unfold mixed expanded
  rw [mul_pow,Real.sq_sqrt hrad]
  simp only [zpow_neg,zpow_natCast,zpow_one]
  field_simp [hx.ne']
  <;> ring

theorem square_convex (a b c k : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hk : 0 ≤ k) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => (mixed a b c k x)^2) := by
  have htwo : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x^(-2 : ℤ)) :=
    (strictConvexOn_zpow (by norm_num : (-2 : ℤ) ≠ 0)
      (by norm_num : (-2 : ℤ) ≠ 1)).convexOn
  have hone : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x^(-1 : ℤ)) :=
    (strictConvexOn_zpow (by norm_num : (-1 : ℤ) ≠ 0)
      (by norm_num : (-1 : ℤ) ≠ 1)).convexOn
  have hlin : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x) := convexOn_id (convex_Ioi 0)
  have hA : 0 ≤ a^2*c := mul_nonneg (sq_nonneg a) hc
  have hB : 0 ≤ a^2*k+2*a*b*c := by positivity
  have hD : 0 ≤ b^2*k := mul_nonneg (sq_nonneg b) hk
  have hsum := (((ConvexOn.smul hA htwo).add (ConvexOn.smul hB hone)).add
    (convexOn_const (2*a*b*k+b^2*c) (convex_Ioi (0 : ℝ)))).add
      (ConvexOn.smul hD hlin)
  have hexp : ConvexOn ℝ (Set.Ioi 0) (expanded a b c k) := by
    simpa only [expanded,Pi.add_apply,smul_eq_mul,id_eq] using hsum
  apply hexp.congr
  intro x hx
  exact (square_expansion a b c k x hc hk hx).symm

theorem le_max_endpoints (a b c k l r x : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hl : 0 < l) (hlx : l ≤ x) (hxr : x ≤ r) :
    mixed a b c k x ≤ max (mixed a b c k l) (mixed a b c k r) := by
  have hr : 0 < r := hl.trans_le (hlx.trans hxr)
  have hx : 0 < x := hl.trans_le hlx
  have hnonneg (v : ℝ) (hv : 0 < v) : 0 ≤ mixed a b c k v :=
    mul_nonneg (add_nonneg (div_nonneg ha hv.le) hb) (Real.sqrt_nonneg _)
  have hmax0 : 0 ≤ max (mixed a b c k l) (mixed a b c k r) :=
    (hnonneg l hl).trans (le_max_left _ _)
  have hsq := (square_convex a b c k ha hb hc hk).le_max_of_mem_Icc hl hr ⟨hlx,hxr⟩
  have hleft : (mixed a b c k l)^2 ≤
      (max (mixed a b c k l) (mixed a b c k r))^2 :=
    (sq_le_sq₀ (hnonneg l hl) hmax0).mpr (le_max_left _ _)
  have hright : (mixed a b c k r)^2 ≤
      (max (mixed a b c k l) (mixed a b c k r))^2 :=
    (sq_le_sq₀ (hnonneg r hr) hmax0).mpr (le_max_right _ _)
  exact (sq_le_sq₀ (hnonneg x hx) hmax0).mp (hsq.trans (max_le hleft hright))

end SymmetricSubgroupAsymptotics.MixedInverseSqrtEndpointBound
