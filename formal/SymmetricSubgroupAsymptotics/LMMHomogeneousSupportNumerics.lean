import SymmetricSubgroupAsymptotics.LMMUniformRectangularLiftCost

/-! Scalar conversion of the complete literal-support/subdirect count.
The automorphism input has the actual cubic logarithmic loss; no
stronger polynomial automorphism-order bound is substituted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Topology
namespace SymmetricSubgroupAsymptotics.LMMHomogeneousSupportNumerics

def supportCount (m u : ℕ) : ℕ := 2^m * (2*(1+m*u))^m

theorem log_supportCount_le (A : ℝ) (hA : 0 ≤ A) (r t m u : ℕ)
    (hr : 2 ≤ r) (ht : 2 ≤ t) (hu : 1 ≤ u)
    (hm : (m : ℝ) ≤ (t : ℝ)*Real.logb 2 (r : ℝ))
    (hauto : Real.logb 2 (u : ℝ) ≤ A*(r : ℝ)*(Real.logb 2 (r : ℝ))^3) :
    Real.logb 2 (supportCount m u : ℝ) ≤
      ((r*t : ℕ) : ℝ)*(3+Real.logb 2 ((r*t : ℕ) : ℝ)) +
        A*((r*t : ℕ) : ℝ)*(Real.logb 2 ((r*t : ℕ) : ℝ))^4 := by
  let n := r*t
  let L := Real.logb 2 (n : ℝ)
  let l := Real.logb 2 (r : ℝ)
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hnp : 0 < (n : ℝ) := by dsimp only [n]; positivity
  have hrp : 0 < (r : ℝ) := by linarith only [hrR]
  have htp : 0 < (t : ℝ) := by linarith only [htR]
  have hup : 0 < (u : ℝ) := by exact_mod_cast (show 0<u by omega)
  have hl : 0 ≤ l := Real.logb_nonneg (by norm_num) (by linarith only [hrR])
  have hrn : (r : ℝ) ≤ n := by
    have hrr : r ≤ r*t := Nat.le_mul_of_pos_right r (by omega)
    exact_mod_cast hrr
  have hlL : l ≤ L := Real.logb_le_logb_of_le (by norm_num) hrp hrn
  have hL : 0 ≤ L := hl.trans hlL
  have hlr : l ≤ r := by
    have hh := BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one r hr
    linarith only [hh]
  have hmn : (m : ℝ) ≤ n := by
    calc
      _ ≤ (t : ℝ)*l := hm
      _ ≤ (t : ℝ)*(r : ℝ) := mul_le_mul_of_nonneg_left hlr htp.le
      _ = (n : ℝ) := by dsimp only [n]; push_cast; ring
  by_cases hm0 : m=0
  · simp only [hm0,supportCount,pow_zero,mul_one,Nat.cast_one,Real.logb_one]
    change (0 : ℝ) ≤ (n : ℝ)*(3+L)+A*(n : ℝ)*L^4
    positivity
  · have hmp : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hlm : Real.logb 2 (m : ℝ) ≤ L :=
      Real.logb_le_logb_of_le (by norm_num) hmp hmn
    have harg : 1+(m : ℝ)*(u : ℝ) ≤ 2*(m : ℝ)*(u : ℝ) := by
      have hmu : (1 : ℝ) ≤ (m : ℝ)*(u : ℝ) := by
        exact_mod_cast (show 1 ≤ m*u from by
          simpa only [one_mul] using Nat.mul_le_mul (show 1 ≤ m by omega) hu)
      linarith only [hmu]
    have hsumlog : Real.logb 2 (1+(m : ℝ)*(u : ℝ)) ≤
        1+Real.logb 2 (m : ℝ)+Real.logb 2 (u : ℝ) := by
      have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
        (by positivity : (0 : ℝ)<1+(m : ℝ)*(u : ℝ)) harg
      simpa only [Real.logb_mul (by positivity : (2 : ℝ)*(m : ℝ)≠0) (ne_of_gt hup),
        Real.logb_mul (by norm_num : (2 : ℝ)≠0) (ne_of_gt hmp),
        Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using hh
    have hlogeq : Real.logb 2 (supportCount m u : ℝ) =
        (m : ℝ)*(2+Real.logb 2 (1+(m : ℝ)*(u : ℝ))) := by
      simp only [supportCount,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
      rw [Real.logb_mul (by positivity : (2 : ℝ)^m≠0)
        (by positivity : (2*(1+(m : ℝ)*(u : ℝ)))^m≠0),
        Real.logb_pow,Real.logb_pow,
        Real.logb_mul (by norm_num : (2 : ℝ)≠0)
          (by positivity : (1+(m : ℝ)*(u : ℝ))≠0),
        Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)]
      ring
    have hmain : (m : ℝ)*Real.logb 2 (u : ℝ) ≤ A*(n : ℝ)*L^4 := by
      calc
        _ ≤ (m : ℝ)*(A*(r : ℝ)*l^3) :=
          mul_le_mul_of_nonneg_left hauto (Nat.cast_nonneg _)
        _ ≤ ((t : ℝ)*l)*(A*(r : ℝ)*l^3) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
        _ = A*(n : ℝ)*l^4 := by dsimp only [n]; push_cast; ring
        _ ≤ A*(n : ℝ)*L^4 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hl hlL 4) (by positivity)
    have hsimple : (m : ℝ)*(3+Real.logb 2 (m : ℝ)) ≤ (n : ℝ)*(3+L) := by
      calc
        _ ≤ (m : ℝ)*(3+L) := mul_le_mul_of_nonneg_left (by linarith only [hlm]) (Nat.cast_nonneg _)
        _ ≤ (n : ℝ)*(3+L) := mul_le_mul_of_nonneg_right hmn (by positivity)
    rw [hlogeq]
    have hh := mul_le_mul_of_nonneg_left hsumlog (Nat.cast_nonneg m)
    change (m : ℝ)*(2+Real.logb 2 (1+(m : ℝ)*(u : ℝ))) ≤
      (n : ℝ)*(3+L)+A*(n : ℝ)*L^4
    nlinarith only [hh,hsimple,hmain]

theorem support_envelope_eventually (A : ℝ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ)*(3+Real.logb 2 (n : ℝ)) + A*(n : ℝ)*(Real.logb 2 (n : ℝ))^4 ≤
        ε*(n : ℝ)^2 := by
  have hzero : Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul,add_zero] using
      (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 0 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hfour : Tendsto (fun n : ℕ => (Real.logb 2 (n : ℝ))^4/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero] using
      (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 4 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ =>
      (3+Real.logb 2 (n : ℝ)+A*(Real.logb 2 (n : ℝ))^4)/(n : ℝ)) atTop (𝓝 0) := by
    convert ((hzero.const_mul 3).add hone).add (hfour.const_mul A) using 1
    · funext n
      ring
    · ring
  filter_upwards [hlim.eventually (eventually_lt_nhds hε),eventually_ge_atTop 2] with n hn htwo
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hh := (div_lt_iff₀ hnp).mp hn
  nlinarith only [mul_le_mul_of_nonneg_left hh.le hnp.le]

theorem uniform_supportCount (A : ℝ) (hA : 0 ≤ A) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ r t m u : ℕ, 2 ≤ r → 2 ≤ t → 1 ≤ u →
      (m : ℝ) ≤ (t : ℝ)*Real.logb 2 (r : ℝ) →
      Real.logb 2 (u : ℝ) ≤ A*(r : ℝ)*(Real.logb 2 (r : ℝ))^3 →
      N ≤ r*t → (supportCount m u : ℝ) ≤ (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (support_envelope_eventually A ε hε)
  refine ⟨N,?_⟩
  intro r t m u hr ht hu hm hauto hn
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
    (by dsimp only [supportCount]; positivity : (0 : ℝ)<supportCount m u)).mp
  exact (log_supportCount_le A hA r t m u hr ht hu hm hauto).trans (hN (r*t) hn)

end SymmetricSubgroupAsymptotics.LMMHomogeneousSupportNumerics
