import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementOneMargin

/-! Small structural arithmetic for two distinct actual primary divisors.
Coprimality excludes the fake dominant values five and six when the
complementary divisor is at least five. The odd endpoint interval is
extended as one whole interval, not by top-degree enumeration. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementArithmetic
open MixedInverseSqrtEndpointBound

theorem primary_ge_seven (q a v : ℕ) (hq : q.Prime) (hv : 5 ≤ v)
    (hvM : v ≤ q^a) (hc : Nat.Coprime (q^a) v) : 7 ≤ q^a := by
  by_contra hh
  have hcases : q^a = 5 ∨ q^a = 6 := by omega
  rcases hcases with h5 | h6
  · have hv5 : v = 5 := by omega
    rw [h5,hv5] at hc
    norm_num at hc
  · have h2 : 2 ∣ q^a := by rw [h6]; decide
    have h3 : 3 ∣ q^a := by rw [h6]; decide
    have hq2 : 2 = q := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)
    have h3q := Nat.prime_three.dvd_of_dvd_pow h3
    rw [← hq2] at h3q
    norm_num at h3q

theorem binary_short_eq_eight (a : ℕ) (hlo : 7 ≤ 2^a) (hhi : 2^a < 16) : 2^a = 8 := by
  have ha3 : a ≤ 3 := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 4 ≤ a by omega)
    norm_num at hpow
    omega
  have ha : a = 3 := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show a ≤ 2 by omega)
    norm_num at hpow
    omega
  rw [ha]
  norm_num

private theorem odd_mixed_le (v : ℝ) (hv : 5 ≤ v) (hv15 : v ≤ 15) :
    mixed (8/7) (3/7) 6 (3/2) v ≤ (11/4 : ℝ) := by
  have hh := le_max_endpoints (8/7) (3/7) 6 (3/2) 5 15 v
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv hv15
  have endpoint (x : ℝ) (hx : 0 < x)
      (hsq : ((8/7 : ℝ)/x+3/7)^2*(6+(3/2)*x) ≤ (11/4 : ℝ)^2) :
      mixed (8/7) (3/7) 6 (3/2) x ≤ (11/4 : ℝ) := by
    apply (sq_le_sq₀ (by unfold mixed; positivity) (by norm_num)).mp
    simpa only [mixed,mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 6+(3/2)*x)] using hsq
  exact hh.trans (max_le (endpoint 5 (by norm_num) (by norm_num))
    (endpoint 15 (by norm_num) (by norm_num)))

theorem odd_short_envelope_le (M v m C L : ℝ)
    (hM : 7 ≤ M) (hv : 5 ≤ v) (hvM : v ≤ M) (hv15 : v ≤ 15)
    (hm : m ≤ 1) (hC : C ≤ 4) (hL : 9/2 ≤ L) (hentropy : L ≤ 4+(3/2)*v) :
    (m/v+(C-m)/M+1/(M*v))*Real.sqrt (2+L)+Real.sqrt (1+2/L) ≤ 4 := by
  have hrate := SmallPrimaryLargeComplementTwoMargins.joint_rate_le M 7 v m C 1 4
    (by norm_num) (by linarith only [hv]) hM hvM hm hC (by norm_num)
  have hmain : (m/v+(C-m)/M+1/(M*v))*Real.sqrt (2+L) ≤ (11/4 : ℝ) := by
    have hh := mul_le_mul hrate
      (Real.sqrt_le_sqrt (by linarith only [hentropy] : 2+L ≤ 6+(3/2)*v))
      (Real.sqrt_nonneg _) (by positivity : 0 ≤ (1+1/(7 : ℝ))/v+(4-1)/7)
    have heq : (1+1/(7 : ℝ))/v+(4-1)/7 = (8/7 : ℝ)/v+3/7 := by ring
    rw [heq] at hh
    exact hh.trans (odd_mixed_le v hv hv15)
  have htop : Real.sqrt (1+2/L) ≤ (11/9 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 9/2) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    linarith only [hh]
  linarith only [hmain,htop]

end SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementArithmetic
