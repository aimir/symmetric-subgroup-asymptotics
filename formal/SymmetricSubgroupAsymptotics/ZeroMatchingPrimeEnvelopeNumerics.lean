import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeSwitchNumerics

/-! A generic zero-matching endpoint tail. The support condition is not
asserted here: the actual matching coefficient must genuinely vanish.
The integer threshold64 and the uniform quadratic margin are proved,
without a prime list or enumeration of top degrees. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ZeroMatchingPrimeEnvelopeNumerics

private theorem polynomial_budget (d : ℕ) (hd : 1 ≤ d) :
    24*d^2+5*d+84 ≤ 60*2^d := by
  induction d,hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
    have hstep : 24*(d+1)^2+5*(d+1)+84 ≤ 2*(24*d^2+5*d+84) := by
      obtain ⟨k,rfl⟩ : ∃ k : ℕ, d = k+1 := ⟨d-1,by omega⟩
      nlinarith only [Nat.zero_le (k^2),Nat.zero_le k]
    calc
      _ ≤ 2*(24*d^2+5*d+84) := hstep
      _ ≤ 2*(60*2^d) := Nat.mul_le_mul_left _ ih
      _ = 60*2^(d+1) := by rw [pow_succ]; ring

theorem quadratic_margin (d : ℕ) (hd : 1 ≤ d) :
    (2/5 : ℝ)*((d : ℝ)^2+1)+1+(d : ℝ)/12 ≤ (2 : ℝ)^d := by
  have hh : 24*(d : ℝ)^2+5*(d : ℝ)+84 ≤ 60*(2 : ℝ)^d := by
    exact_mod_cast polynomial_budget d hd
  nlinarith only [hh]

theorem envelope_le (M d : ℕ) (hM : 64 ≤ M) (hd1 : 1 ≤ d) (hd6 : d ≤ 6)
    (C v : ℝ) (hC : C ≤ (d : ℝ)^2)
    (hv0 : 0 ≤ v) (hvM : v ≤ M) :
    ((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+Real.logb 2 (M : ℝ)+8*v) +
      Real.sqrt (1+(d : ℝ)/Real.logb 2 (M : ℝ)) ≤ (2 : ℝ)^d := by
  have hMR : (64 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hdR6 : (d : ℝ) ≤ 6 := by exact_mod_cast hd6
  have hlog := BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one M (by omega)
  have hL6 : (6 : ℝ) ≤ Real.logb 2 (M : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 64) hMR
    have heq : Real.logb 2 (64 : ℝ) = 6 := by
      rw [show (64 : ℝ) = 2^6 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      norm_num
    simpa only [heq] using hh
  have hlog0 : 0 ≤ Real.logb 2 (M : ℝ) := by linarith
  have hrad0 : 0 ≤ (d : ℝ)+Real.logb 2 (M : ℝ)+8*v :=
    add_nonneg (add_nonneg hd0 hlog0) (mul_nonneg (by norm_num) hv0)
  have hrad : (d : ℝ)+Real.logb 2 (M : ℝ)+8*v ≤ 10*(M : ℝ) := by linarith
  have hquad := mul_le_mul_of_nonneg_right hMR hM0.le
  have hs : Real.sqrt ((d : ℝ)+Real.logb 2 (M : ℝ)+8*v) ≤ (2/5)*(M : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hrad,hquad,hM0.le]
  have hsdiv : Real.sqrt ((d : ℝ)+Real.logb 2 (M : ℝ)+8*v)/(M : ℝ) ≤ 2/5 :=
    (div_le_iff₀ hM0).mpr hs
  have hfirst : ((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+Real.logb 2 (M : ℝ)+8*v) ≤
      ((d : ℝ)^2+1)*(2/5) := by
    have hh := mul_le_mul (add_le_add hC le_rfl) hsdiv
      (div_nonneg (Real.sqrt_nonneg _) hM0.le) (by positivity : 0 ≤ (d : ℝ)^2+1)
    convert hh using 1 <;> ring
  have hratio : Real.sqrt (1+(d : ℝ)/Real.logb 2 (M : ℝ)) ≤ 1+(d : ℝ)/12 := by
    have hh := div_le_div_of_nonneg_left hd0 (by norm_num : (0 : ℝ) < 6) hL6
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_nonneg (d : ℝ)]
  have hmargin := quadratic_margin d hd1
  nlinarith only [hfirst,hratio,hmargin]

end SymmetricSubgroupAsymptotics.ZeroMatchingPrimeEnvelopeNumerics
