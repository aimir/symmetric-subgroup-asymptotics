import SymmetricSubgroupAsymptotics.MixedInverseSqrtEndpointBound

/-! A capped divisor rate together with the reciprocal error from the
actual complementary divisor. The same variable occurs in both terms.
Splitting at the cap switch gives two of the already proved convex-square
mixed envelopes, so only endpoints and the switch are needed. There is
no finite grid, prime-power cutoff or group-generation hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CappedReciprocalErrorEndpointBound
open MixedInverseSqrtEndpointBound

def envelope (m u b e c k x : ℝ) : ℝ :=
  (m*min u (1/x)+b+e/x)*Real.sqrt (c+k*x)

private theorem below_switch (m u b e c k x : ℝ)
    (hu : 0 < u) (hx : 0 < x) (hxs : x ≤ 1/u) :
    envelope m u b e c k x = mixed e (m*u+b) c k x := by
  have hux : u ≤ 1/x := (le_div_iff₀ hx).mpr (by
    have hh := (le_div_iff₀ hu).mp hxs
    nlinarith)
  unfold envelope mixed
  rw [min_eq_left hux]
  ring

private theorem above_switch (m u b e c k x : ℝ)
    (hu : 0 < u) (hx : 0 < x) (hsx : 1/u ≤ x) :
    envelope m u b e c k x = mixed (m+e) b c k x := by
  have hxu : 1/x ≤ u := (div_le_iff₀ hx).mpr (by
    have hh := (div_le_iff₀ hu).mp hsx
    nlinarith)
  unfold envelope mixed
  rw [min_eq_right hxu]
  simp only [div_eq_mul_inv,one_mul]
  ring

theorem le_max_endpoints_and_switch (m u b e c k l r x : ℝ)
    (hm : 0 ≤ m) (hu : 0 < u) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hc : 0 ≤ c) (hk : 0 ≤ k) (hl : 0 < l) (hlx : l ≤ x) (hxr : x ≤ r) :
    envelope m u b e c k x ≤
      max (envelope m u b e c k l)
        (max (envelope m u b e c k (1/u)) (envelope m u b e c k r)) := by
  have hx : 0 < x := hl.trans_le hlx
  have hr : 0 < r := hx.trans_le hxr
  have hs : 0 < 1/u := one_div_pos.mpr hu
  by_cases hxs : x ≤ 1/u
  · have hls : l ≤ 1/u := hlx.trans hxs
    have hh := MixedInverseSqrtEndpointBound.le_max_endpoints
      e (m*u+b) c k l (1/u) x he
      (add_nonneg (mul_nonneg hm hu.le) hb) hc hk hl hlx hxs
    rw [← below_switch m u b e c k x hu hx hxs,
      ← below_switch m u b e c k l hu hl hls,
      ← below_switch m u b e c k (1/u) hu hs le_rfl] at hh
    exact hh.trans (max_le (le_max_left _ _)
      ((le_max_left _ _).trans (le_max_right _ _)))
  · have hsx : 1/u ≤ x := (lt_of_not_ge hxs).le
    have hsr : 1/u ≤ r := hsx.trans hxr
    have hh := MixedInverseSqrtEndpointBound.le_max_endpoints
      (m+e) b c k (1/u) r x (add_nonneg hm he) hb hc hk hs hsx hxr
    rw [← above_switch m u b e c k x hu hx hsx,
      ← above_switch m u b e c k (1/u) hu hs le_rfl,
      ← above_switch m u b e c k r hu hr hsr] at hh
    exact hh.trans (le_max_right _ _)

end SymmetricSubgroupAsymptotics.CappedReciprocalErrorEndpointBound
