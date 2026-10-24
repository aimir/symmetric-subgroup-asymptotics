import SymmetricSubgroupAsymptotics.BinaryAffineArbitraryTopTailNumerics
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorNumerics

/-! A real two-regime aggregate for arbitrary top degrees. The hypotheses
are the actual half/log cost estimates, not a global permutation-generator
input. Scalar polynomial budgets hold uniformly in dimension at least7. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineArbitraryTopRealTail

private theorem four_pow_eq_two_pow_square (d : ℕ) :
    (4 : ℝ)^d = ((2 : ℝ)^d)^2 := by
  calc
    (4 : ℝ)^d = ((2 : ℝ)^2)^d := by norm_num
    _ = (2 : ℝ)^(2*d) := (pow_mul _ _ _).symm
    _ = (2 : ℝ)^(d*2) := by rw [Nat.mul_comm]
    _ = ((2 : ℝ)^d)^2 := pow_mul _ _ _

theorem aggregate_le (d : ℕ) (hd : 7 ≤ d) (t g : ℝ) (ht : 2 ≤ t)
    (hhalf : g ≤ (d : ℝ)^2*t/2 + (⌈t/Real.sqrt (Real.logb 2 t)⌉₊ : ℝ))
    (hlog : g ≤ 2*(d : ℝ)^2*t/Real.sqrt (Real.logb 2 t) +
      (⌈t/Real.sqrt (Real.logb 2 t)⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*t/Real.sqrt ((d : ℝ)+Real.logb 2 t) := by
  let L := Real.logb 2 t
  have ht0 : 0 ≤ t := by linarith
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hL1 : 1 ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) ht
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hL : 0 < L := by linarith
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hds : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by linarith)
  have hLsq : (Real.sqrt L)^2 = L := Real.sq_sqrt hL.le
  have hdsq : (Real.sqrt ((d : ℝ)+L))^2 = (d : ℝ)+L :=
    Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt L := by
    have hh := Real.sqrt_le_sqrt hL1
    simpa only [Real.sqrt_one] using hh
  have hsle : Real.sqrt L ≤ t :=
    (Real.sqrt_le_iff).mpr ⟨ht0,LargeOrbitGeneratorNumerics.logb_le_square ht⟩
  have hunit : (1 : ℝ) ≤ t/Real.sqrt L := (le_div_iff₀ hs).mpr (by simpa using hsle)
  have hnonneg : 0 ≤ t/Real.sqrt L := div_nonneg ht0 hs.le
  have hceil : (⌈t/Real.sqrt L⌉₊ : ℝ) ≤ t/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one hnonneg).le
  have hpow0 : 0 ≤ (2 : ℝ)^d := by positivity
  change g ≤ (2 : ℝ)^d*t/Real.sqrt ((d : ℝ)+L)
  change g ≤ (d : ℝ)^2*t/2 + (⌈t/Real.sqrt L⌉₊ : ℝ) at hhalf
  change g ≤ 2*(d : ℝ)^2*t/Real.sqrt L + (⌈t/Real.sqrt L⌉₊ : ℝ) at hlog
  by_cases hsmall : L ≤ 2*(d : ℝ)
  · have hb : 3*(d : ℝ)*((d : ℝ)^2+4)^2 ≤ 4*((2 : ℝ)^d)^2 := by
      have hh := BinaryAffineArbitraryTopTailNumerics.small_log_budget d hd
      have hhR : 3*(d : ℝ)*((d : ℝ)^2+4)^2 ≤ 4*(4 : ℝ)^d := by exact_mod_cast hh
      simpa only [four_pow_eq_two_pow_square] using hhR
    have hc0 : 0 ≤ (d : ℝ)^2/2+2 := by positivity
    have hcoefSq : (((d : ℝ)^2/2+2)*Real.sqrt ((d : ℝ)+L))^2 ≤
        ((2 : ℝ)^d)^2 := by
      calc
        _ = ((d : ℝ)^2/2+2)^2*((d : ℝ)+L) := by rw [mul_pow,hdsq]
        _ ≤ ((d : ℝ)^2/2+2)^2*(3*(d : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
        _ ≤ ((2 : ℝ)^d)^2 := by nlinarith only [hb]
    have hcoef : ((d : ℝ)^2/2+2)*Real.sqrt ((d : ℝ)+L) ≤ (2 : ℝ)^d :=
      (sq_le_sq₀ (mul_nonneg hc0 hds.le) hpow0).mp hcoefSq
    have hdiv : t/Real.sqrt L ≤ t := (div_le_iff₀ hs).mpr (by nlinarith)
    have hg : g ≤ ((d : ℝ)^2/2+2)*t := by nlinarith [hhalf,hceil]
    apply (le_div_iff₀ hds).mpr
    calc
      g*Real.sqrt ((d : ℝ)+L) ≤
          (((d : ℝ)^2/2+2)*t)*Real.sqrt ((d : ℝ)+L) :=
        mul_le_mul_of_nonneg_right hg hds.le
      _ = (((d : ℝ)^2/2+2)*Real.sqrt ((d : ℝ)+L))*t := by ring
      _ ≤ (2 : ℝ)^d*t := mul_le_mul_of_nonneg_right hcoef ht0
  · have hlarge : 2*(d : ℝ) ≤ L := by linarith
    have hb : 3*(2*(d : ℝ)^2+2)^2 ≤ 2*((2 : ℝ)^d)^2 := by
      have hh := BinaryAffineArbitraryTopTailNumerics.large_log_budget d hd
      have hhR : 3*(2*(d : ℝ)^2+2)^2 ≤ 2*(4 : ℝ)^d := by exact_mod_cast hh
      simpa only [four_pow_eq_two_pow_square] using hhR
    have hc0 : 0 ≤ 2*(d : ℝ)^2+2 := by positivity
    have hcoefSq : ((2*(d : ℝ)^2+2)*Real.sqrt ((d : ℝ)+L))^2 ≤
        ((2 : ℝ)^d*Real.sqrt L)^2 := by
      have hmul := mul_le_mul_of_nonneg_right hb hL.le
      rw [mul_pow,hdsq,mul_pow,hLsq]
      nlinarith only [hmul,hlarge,mul_nonneg (sq_nonneg (2*(d : ℝ)^2+2))
        (show 0 ≤ L-2*(d : ℝ) by linarith)]
    have hcoef : (2*(d : ℝ)^2+2)*Real.sqrt ((d : ℝ)+L) ≤
        (2 : ℝ)^d*Real.sqrt L :=
      (sq_le_sq₀ (mul_nonneg hc0 hds.le) (mul_nonneg hpow0 hs.le)).mp hcoefSq
    have hunit2 : t/Real.sqrt L+1 ≤ 2*(t/Real.sqrt L) := by
      linarith only [hunit]
    have hg : g ≤ (2*(d : ℝ)^2+2)*t/Real.sqrt L := by
      calc
        g ≤ 2*(d : ℝ)^2*t/Real.sqrt L + (⌈t/Real.sqrt L⌉₊ : ℝ) := hlog
        _ ≤ 2*(d : ℝ)^2*t/Real.sqrt L + (t/Real.sqrt L+1) :=
          add_le_add le_rfl hceil
        _ ≤ 2*(d : ℝ)^2*t/Real.sqrt L + 2*(t/Real.sqrt L) :=
          add_le_add le_rfl hunit2
        _ = (2*(d : ℝ)^2+2)*t/Real.sqrt L := by ring
    apply (le_div_iff₀ hds).mpr
    calc
      g*Real.sqrt ((d : ℝ)+L) ≤
          ((2*(d : ℝ)^2+2)*t/Real.sqrt L)*Real.sqrt ((d : ℝ)+L) :=
        mul_le_mul_of_nonneg_right hg hds.le
      _ = ((2*(d : ℝ)^2+2)*Real.sqrt ((d : ℝ)+L))*t/Real.sqrt L := by ring
      _ ≤ ((2 : ℝ)^d*Real.sqrt L)*t/Real.sqrt L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef ht0) hs.le
      _ = (2 : ℝ)^d*t := by
        rw [mul_right_comm,mul_div_cancel_right₀ _ hs.ne']

end SymmetricSubgroupAsymptotics.BinaryAffineArbitraryTopRealTail
