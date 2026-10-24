import SymmetricSubgroupAsymptotics.MixedInverseSqrtEndpointBound

/-! The actual capped inverse-rate envelope is controlled by its cap
switch and right endpoint. This retains the whole interval, including a
switch outside it; it introduces no exponent cutoff or finite grid. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CappedInverseSqrtEndpointBound
open MixedInverseSqrtEndpointBound

def capped (m u b c k x : ℝ) : ℝ :=
  (m*min u (1/x)+b)*Real.sqrt (c+k*x)

private theorem mixed_at_switch (m u b c k : ℝ) :
    mixed m b c k (1/u) = (m*u+b)*Real.sqrt (c+k*(1/u)) := by
  simp only [mixed,div_div_eq_mul_div,div_one]

theorem le_switch_or_right (m u b c k r x : ℝ)
    (hm : 0 ≤ m) (hu : 0 < u) (hb : 0 ≤ b) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hx : 0 < x) (hxr : x ≤ r) :
    capped m u b c k x ≤
      max ((m*u+b)*Real.sqrt (c+k*(1/u)))
        ((m/r+b)*Real.sqrt (c+k*r)) := by
  have hs : 0 < 1/u := one_div_pos.mpr hu
  by_cases hxs : x ≤ 1/u
  · have hcoef : m*min u (1/x)+b ≤ m*u+b :=
      add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) hm) le_rfl
    have hrad : c+k*x ≤ c+k*(1/u) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hxs hk)
    have hstep : capped m u b c k x ≤
        (m*u+b)*Real.sqrt (c+k*(1/u)) := by
      exact mul_le_mul hcoef (Real.sqrt_le_sqrt hrad)
        (Real.sqrt_nonneg _) (add_nonneg (mul_nonneg hm hu.le) hb)
    exact hstep.trans (le_max_left _ _)
  · have hsx : 1/u ≤ x := le_of_lt (lt_of_not_ge hxs)
    have hcoef : m*min u (1/x)+b ≤ m/x+b := by
      simpa only [div_eq_mul_inv,one_mul] using
        add_le_add (mul_le_mul_of_nonneg_left (min_le_right u (1/x)) hm) le_rfl
    have hstep : capped m u b c k x ≤ mixed m b c k x :=
      mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
    have hmax := MixedInverseSqrtEndpointBound.le_max_endpoints
      m b c k (1/u) r x hm hb hc hk hs hsx hxr
    rw [mixed_at_switch] at hmax
    exact hstep.trans hmax

end SymmetricSubgroupAsymptotics.CappedInverseSqrtEndpointBound
