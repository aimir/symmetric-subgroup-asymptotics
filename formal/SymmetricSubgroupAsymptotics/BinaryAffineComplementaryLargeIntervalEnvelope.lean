import SymmetricSubgroupAsymptotics.BinaryAffineComplementaryLargeIntervalMargins
import SymmetricSubgroupAsymptotics.MixedInverseSqrtEndpointBound
import SymmetricSubgroupAsymptotics.ZeroMatchingPrimeEnvelopeNumerics

/-! A uniform complementary-divisor interval, with only two ranges for
the dominant power. Actual GL coefficients and logarithmic bounds are
retained. No scalar-fit conclusion, exponent grid or action table is an
input. The right endpoint reuses the proved zero-matching envelope. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineComplementaryLargeIntervalEnvelope
open BinaryAffineComplementaryLargeIntervalMargins

theorem envelope_le (M d : ℕ) (hM : 64 ≤ M) (hd1 : 1 ≤ d) (hd6 : d ≤ 6)
    (C m v : ℝ) (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2)
    (hv : 16 ≤ v) (hvM : v ≤ M)
    (hlog : Real.logb 2 (M : ℝ) ≤ 127 ∨
      (m ≤ (d : ℝ)-1 ∧ Real.logb 2 (M : ℝ) ≤ 635)) :
    (m/v+(C-m+1)/(M : ℝ))*
        Real.sqrt ((d : ℝ)+Real.logb 2 (M : ℝ)+(17/4)*v) +
      Real.sqrt (1+(d : ℝ)/Real.logb 2 (M : ℝ)) ≤ (2 : ℝ)^d := by
  let L := Real.logb 2 (M : ℝ)
  let b := (C-m+1)/(M : ℝ)
  have hMR : (64 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hdR6 : (d : ℝ) ≤ 6 := by exact_mod_cast hd6
  have hB0 : 0 ≤ C-m+1 := by linarith
  have hb : 0 ≤ b := div_nonneg hB0 hM0.le
  have hL6 : (6 : ℝ) ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 64) hMR
    have heq : Real.logb 2 (64 : ℝ) = 6 := by
      rw [show (64 : ℝ) = 2^6 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      norm_num
    simpa only [heq,L] using hh
  have htop6 : Real.sqrt (1+(d : ℝ)/L) ≤ 1+(d : ℝ)/12 := by
    have hh := div_le_div_of_nonneg_left hd0 (by norm_num : (0 : ℝ) < 6) hL6
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_nonneg (d : ℝ)]
  have hright : MixedInverseSqrtEndpointBound.mixed m b ((d : ℝ)+L) (17/4) M +
      Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
    have hh := ZeroMatchingPrimeEnvelopeNumerics.envelope_le M d hM hd1 hd6 C
      (M : ℝ) hC hM0.le le_rfl
    have heq : m/(M : ℝ)+b = (C+1)/(M : ℝ) := by dsimp only [b]; ring
    unfold MixedInverseSqrtEndpointBound.mixed
    rw [heq]
    have hrad : (d : ℝ)+L+(17/4)*(M : ℝ) ≤ (d : ℝ)+L+8*(M : ℝ) := by
      nlinarith only [hM0.le]
    have hfirst := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad)
      (div_nonneg (by linarith : 0 ≤ C+1) hM0.le)
    exact (add_le_add hfirst le_rfl).trans hh
  have hleft : MixedInverseSqrtEndpointBound.mixed m b ((d : ℝ)+L) (17/4) 16 +
      Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
    by_cases hsmall : M ≤ 1024
    · have hL10 : L ≤ 10 := by
        have hupper : (M : ℝ) ≤ 1024 := by exact_mod_cast hsmall
        have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hM0 hupper
        have heq : Real.logb 2 (1024 : ℝ) = 10 := by
          rw [show (1024 : ℝ) = 2^10 by norm_num,Real.logb_pow,
            Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
          norm_num
        simpa only [heq,L] using hh
      have hdiv := div_le_div_of_nonneg_left hB0 (by norm_num : (0 : ℝ) < 64) hMR
      have hcoef : m/16+b ≤
          (3*((d : ℝ)*((d : ℝ)+1)/2)+(d : ℝ)^2+1)/64 := by
        dsimp only [b]
        linarith only [hdiv,hmA,hC]
      have hsqrt : Real.sqrt ((d : ℝ)+L+(17/4)*16) ≤ ((d : ℝ)+162)/18 := by
        apply Real.sqrt_le_iff.mpr
        refine ⟨by positivity,?_⟩
        nlinarith [sq_nonneg (d : ℝ)]
      have hfirst := mul_le_mul hcoef hsqrt (Real.sqrt_nonneg _)
        (by positivity : 0 ≤ (3*((d : ℝ)*((d : ℝ)+1)/2)+(d : ℝ)^2+1)/64)
      calc
        MixedInverseSqrtEndpointBound.mixed m b ((d : ℝ)+L) (17/4) 16 +
            Real.sqrt (1+(d : ℝ)/L) ≤
            ((3*((d : ℝ)*((d : ℝ)+1)/2)+(d : ℝ)^2+1)/64)*
              (((d : ℝ)+162)/18)+(1+(d : ℝ)/12) := add_le_add hfirst htop6
        _ = smallBudget d := by unfold smallBudget; ring
        _ ≤ (2 : ℝ)^d := smallBudget_le d hd1
    · have hlarge : (1024 : ℝ) ≤ M := by exact_mod_cast (show 1024 ≤ M by omega)
      have hL10 : (10 : ℝ) ≤ L := by
        have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (by norm_num : (0 : ℝ) < 1024) hlarge
        have heq : Real.logb 2 (1024 : ℝ) = 10 := by
          rw [show (1024 : ℝ) = 2^10 by norm_num,Real.logb_pow,
            Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
          norm_num
        simpa only [heq,L] using hh
      have htop10 : Real.sqrt (1+(d : ℝ)/L) ≤ 1+(d : ℝ)/20 := by
        have hh := div_le_div_of_nonneg_left hd0 (by norm_num : (0 : ℝ) < 10) hL10
        apply Real.sqrt_le_iff.mpr
        refine ⟨by positivity,?_⟩
        nlinarith [sq_nonneg (d : ℝ)]
      have hdiv := div_le_div_of_nonneg_left hB0 (by norm_num : (0 : ℝ) < 1024) hlarge
      rcases hlog with hbinary | ⟨hodd,hlog⟩
      · have hcoef : m/16+b ≤
            (63*((d : ℝ)*((d : ℝ)+1)/2)+(d : ℝ)^2+1)/1024 := by
          dsimp only [b]
          linarith only [hdiv,hmA,hC]
        have hsqrt : Real.sqrt ((d : ℝ)+L+(17/4)*16) ≤ ((d : ℝ)+392)/28 := by
          apply Real.sqrt_le_iff.mpr
          refine ⟨by positivity,?_⟩
          change Real.logb 2 (M : ℝ) ≤ 127 at hbinary
          dsimp only [L]
          nlinarith [sq_nonneg (d : ℝ)]
        have hfirst := mul_le_mul hcoef hsqrt (Real.sqrt_nonneg _)
          (by positivity : 0 ≤ (63*((d : ℝ)*((d : ℝ)+1)/2)+(d : ℝ)^2+1)/1024)
        calc
          MixedInverseSqrtEndpointBound.mixed m b ((d : ℝ)+L) (17/4) 16 +
              Real.sqrt (1+(d : ℝ)/L) ≤
              ((63*((d : ℝ)*((d : ℝ)+1)/2)+(d : ℝ)^2+1)/1024)*
                (((d : ℝ)+392)/28)+(1+(d : ℝ)/20) := add_le_add hfirst htop10
          _ = binaryBudget d := by unfold binaryBudget; ring
          _ ≤ (2 : ℝ)^d := binaryBudget_le d hd1
      · have hcoef : m/16+b ≤ (63*((d : ℝ)-1)+(d : ℝ)^2+1)/1024 := by
          dsimp only [b]
          linarith only [hdiv,hodd,hC]
        have hdR1 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        have hnum : 0 ≤ 63*((d : ℝ)-1)+(d : ℝ)^2+1 := by nlinarith
        have hsqrt : Real.sqrt ((d : ℝ)+L+(17/4)*16) ≤ ((d : ℝ)+1458)/54 := by
          apply Real.sqrt_le_iff.mpr
          refine ⟨by positivity,?_⟩
          dsimp only [L]
          nlinarith [sq_nonneg (d : ℝ)]
        have hfirst := mul_le_mul hcoef hsqrt (Real.sqrt_nonneg _)
          (div_nonneg hnum (by norm_num))
        calc
          MixedInverseSqrtEndpointBound.mixed m b ((d : ℝ)+L) (17/4) 16 +
              Real.sqrt (1+(d : ℝ)/L) ≤
              ((63*((d : ℝ)-1)+(d : ℝ)^2+1)/1024)*
                (((d : ℝ)+1458)/54)+(1+(d : ℝ)/20) := add_le_add hfirst htop10
          _ = oddBudget d := by unfold oddBudget; ring
          _ ≤ (2 : ℝ)^d := oddBudget_le d hd1
  have hh := MixedInverseSqrtEndpointBound.le_max_endpoints m b ((d : ℝ)+L) (17/4)
    16 (M : ℝ) v hm0 hb (by linarith only [hd0,hL6]) (by norm_num)
      (by norm_num) hv hvM
  have hmax : max
      (MixedInverseSqrtEndpointBound.mixed m b ((d : ℝ)+L) (17/4) 16)
      (MixedInverseSqrtEndpointBound.mixed m b ((d : ℝ)+L) (17/4) M) ≤
        (2 : ℝ)^d-Real.sqrt (1+(d : ℝ)/L) :=
    max_le (by linarith only [hleft]) (by linarith only [hright])
  have hfinal := hh.trans hmax
  dsimp only [MixedInverseSqrtEndpointBound.mixed,b,L] at hfinal
  linarith only [hfinal]

end SymmetricSubgroupAsymptotics.BinaryAffineComplementaryLargeIntervalEnvelope
