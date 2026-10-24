import SymmetricSubgroupAsymptotics.CoarseTopCeilingRelativeError

/-! Uniform scalar intervals for the SAME order-six joint chief cost.
The largest primary>=8 regime and the nonmatching small-primary regime
are both paid without a top-degree grid. Five tiny top degrees are left
for exact integer ceiling certificates in the original installer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OrderSixJointCoarseCeilingNumerics

private theorem interval_coefficient_le (A B s L R H : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) (hL : 0 < L)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hroot : L ≤ R^2)
    (hratio : s+L ≤ H^2*L) (hnum : (A*R+B)*H ≤ 3) :
    (A+B/Real.sqrt L)*Real.sqrt (s+L) ≤ 3 := by
  have hrootPos := Real.sqrt_pos.mpr hL
  have hrootR : Real.sqrt L ≤ R := (Real.sqrt_le_iff).mpr ⟨hR,hroot⟩
  have hratioRoot : Real.sqrt (s+L) ≤ H*Real.sqrt L := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hH hrootPos.le)).mp
    rw [Real.sq_sqrt (by linarith only [hs,hL]),mul_pow,Real.sq_sqrt hL.le]
    exact hratio
  calc
    (A+B/Real.sqrt L)*Real.sqrt (s+L) ≤ (A+B/Real.sqrt L)*(H*Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hratioRoot (by positivity)
    _ = (A*Real.sqrt L+B)*H := by field_simp [hrootPos.ne'] <;> ring
    _ ≤ (A*R+B)*H := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hrootR hA) le_rfl) hH
    _ ≤ 3 := hnum

private theorem low_log_coefficient (s L : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 8/5)
    (hL4 : 4 ≤ L) (hL10 : L ≤ 10) :
    (1/2+(9/8)/Real.sqrt L)*Real.sqrt (s+L) ≤ 3 := by
  by_cases h6 : L ≤ 6
  · exact interval_coefficient_le (1/2) (9/8) s L (5/2) (6/5)
      (by norm_num) (by norm_num) hs0 (by linarith only [hL4])
      (by norm_num) (by norm_num) (by nlinarith only [h6])
      (by nlinarith only [hs,hL4]) (by norm_num)
  · have hL6 : 6 ≤ L := by linarith only [h6]
    by_cases h8 : L ≤ 8
    · exact interval_coefficient_le (1/2) (9/8) s L (17/6) (17/15)
        (by norm_num) (by norm_num) hs0 (by linarith only [hL6])
        (by norm_num) (by norm_num) (by nlinarith only [h8])
        (by nlinarith only [hs,hL6]) (by norm_num)
    · have hL8 : 8 ≤ L := by linarith only [h8]
      exact interval_coefficient_le (1/2) (9/8) s L (16/5) (11/10)
        (by norm_num) (by norm_num) hs0 (by linarith only [hL8])
        (by norm_num) (by norm_num) (by nlinarith only [hL10])
        (by nlinarith only [hs,hL8]) (by norm_num)

theorem large_primary_aggregate (t : ℕ) (ht : 8 ≤ t) (s g : ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 8/5)
    (hhalf : g ≤ (t : ℝ)/2+(⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ))
    (hlog : g ≤ (8/5)*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ 3*(t : ℝ)/Real.sqrt (s+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  have htR : (8 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hL3 : 3 ≤ L := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 3 (by omega)
      (by decide) (by simpa only [pow_one] using ht)
    simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using hh
  have hL : 0 < L := by linarith only [hL3]
  have hrootL := Real.sqrt_pos.mpr hL
  have hrootS := Real.sqrt_pos.mpr (show 0 < s+L by linarith only [hs0,hL])
  change g ≤ (t : ℝ)/2+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hhalf
  change g ≤ (8/5)*(t : ℝ)/Real.sqrt L+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hlog
  change g ≤ 3*(t : ℝ)/Real.sqrt (s+L)
  by_cases h16 : t ≤ 16
  · have hL4 : L ≤ 4 := by
      have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 4 (by omega)
        (by decide) (by simpa only [pow_one] using h16)
      simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using hh
    have hrootLower : (5/3 : ℝ) ≤ Real.sqrt L := by
      nlinarith only [Real.sq_sqrt hL.le,Real.sqrt_nonneg L,hL3]
    have hdiv : (t : ℝ)/Real.sqrt L ≤ (3/5)*(t : ℝ) := by
      apply (div_le_iff₀ hrootL).mpr
      have hh := mul_le_mul_of_nonneg_left hrootLower ht0
      nlinarith only [hh]
    have hceil := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (t : ℝ)/Real.sqrt L by positivity)).le
    have hceil' : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (3/4)*(t : ℝ) := by
      linarith only [hceil,hdiv,htR]
    have hg : g ≤ (5/4)*(t : ℝ) := by linarith only [hhalf,hceil']
    have hrootUpper : Real.sqrt (s+L) ≤ (12/5 : ℝ) :=
      (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith only [hs,hL4]⟩
    apply (le_div_iff₀ hrootS).mpr
    calc
      g*Real.sqrt (s+L) ≤ ((5/4)*(t : ℝ))*Real.sqrt (s+L) :=
        mul_le_mul_of_nonneg_right hg hrootS.le
      _ ≤ ((5/4)*(t : ℝ))*(12/5) :=
        mul_le_mul_of_nonneg_left hrootUpper (by positivity)
      _ = 3*(t : ℝ) := by ring
  · have ht16 : 16 ≤ t := by omega
    have hL4 : 4 ≤ L := by
      have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 4 (by omega)
        (by decide) (by simpa only [pow_one] using ht16)
      simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using hh
    have hceil := CoarseTopCeilingRelativeError.ceil_le_nine_eighths t ht16
    change (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (9/8)*((t : ℝ)/Real.sqrt L) at hceil
    by_cases h10 : L ≤ 10
    · have hcoef := low_log_coefficient s L hs0 hs hL4 h10
      have hg : g ≤ (1/2+(9/8)/Real.sqrt L)*(t : ℝ) := by
        have hh := hhalf.trans (add_le_add le_rfl hceil)
        convert hh using 1 <;> ring
      apply (le_div_iff₀ hrootS).mpr
      calc
        g*Real.sqrt (s+L) ≤ ((1/2+(9/8)/Real.sqrt L)*(t : ℝ))*Real.sqrt (s+L) :=
          mul_le_mul_of_nonneg_right hg hrootS.le
        _ = ((1/2+(9/8)/Real.sqrt L)*Real.sqrt (s+L))*(t : ℝ) := by ring
        _ ≤ 3*(t : ℝ) := mul_le_mul_of_nonneg_right hcoef ht0
    · have hL10 : 10 ≤ L := by linarith only [h10]
      have hg : g ≤ (109/40)*(t : ℝ)/Real.sqrt L := by
        have hh := hlog.trans (add_le_add le_rfl hceil)
        convert hh using 1 <;> ring
      have hcoef : (109/40)*Real.sqrt (s+L) ≤ 3*Real.sqrt L := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).mp
        rw [mul_pow,mul_pow,Real.sq_sqrt (by linarith only [hs0,hL]),Real.sq_sqrt hL.le]
        nlinarith only [hs,hL10]
      apply (le_div_iff₀ hrootS).mpr
      calc
        g*Real.sqrt (s+L) ≤ ((109/40)*(t : ℝ)/Real.sqrt L)*Real.sqrt (s+L) :=
          mul_le_mul_of_nonneg_right hg hrootS.le
        _ = ((109/40)*Real.sqrt (s+L))*(t : ℝ)/Real.sqrt L := by ring
        _ ≤ (3*Real.sqrt L)*(t : ℝ)/Real.sqrt L :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef ht0) hrootL.le
        _ = 3*(t : ℝ) := by field_simp [hrootL.ne']

private theorem nonmatching_coefficient (s L : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 8/5)
    (hL2 : 2 ≤ L) (hL9 : L ≤ 9) :
    (2/5+(3/2)/Real.sqrt L)*Real.sqrt (s+L) ≤ 3 := by
  by_cases h3 : L ≤ 3
  · exact interval_coefficient_le (2/5) (3/2) s L (7/4) (27/20)
      (by norm_num) (by norm_num) hs0 (by linarith only [hL2])
      (by norm_num) (by norm_num) (by nlinarith only [h3])
      (by nlinarith only [hs,hL2]) (by norm_num)
  · have hL3 : 3 ≤ L := by linarith only [h3]
    by_cases h5 : L ≤ 5
    · exact interval_coefficient_le (2/5) (3/2) s L (9/4) (5/4)
        (by norm_num) (by norm_num) hs0 (by linarith only [hL3])
        (by norm_num) (by norm_num) (by nlinarith only [h5])
        (by nlinarith only [hs,hL3]) (by norm_num)
    · have hL5 : 5 ≤ L := by linarith only [h5]
      by_cases h7 : L ≤ 7
      · exact interval_coefficient_le (2/5) (3/2) s L (8/3) (23/20)
          (by norm_num) (by norm_num) hs0 (by linarith only [hL5])
          (by norm_num) (by norm_num) (by nlinarith only [h7])
          (by nlinarith only [hs,hL5]) (by norm_num)
      · have hL7 : 7 ≤ L := by linarith only [h7]
        exact interval_coefficient_le (2/5) (3/2) s L 3 (10/9)
          (by norm_num) (by norm_num) hs0 (by linarith only [hL7])
          (by norm_num) (by norm_num) (by nlinarith only [hL9])
          (by nlinarith only [hs,hL7]) (by norm_num)

theorem small_nonmatching_aggregate (t : ℕ) (ht : 4 ≤ t) (s g : ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 8/5) (hL9 : Real.logb 2 (t : ℝ) ≤ 9)
    (hcost : g ≤ (2/5)*(t : ℝ)+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ 3*(t : ℝ)/Real.sqrt (s+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  have hL2 : 2 ≤ L := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 2 (by omega)
      (by decide) (by simpa only [pow_one] using ht)
    simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using hh
  have hL : 0 < L := by linarith only [hL2]
  have hrootS := Real.sqrt_pos.mpr (show 0 < s+L by linarith only [hs0,hL])
  have hceil := CoarseTopCeilingRelativeError.ceil_le_three_halves t (by omega)
  change (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (3/2)*((t : ℝ)/Real.sqrt L) at hceil
  have hcoef := nonmatching_coefficient s L hs0 hs hL2 hL9
  have hg : g ≤ (2/5+(3/2)/Real.sqrt L)*(t : ℝ) := by
    have hh := hcost.trans (add_le_add le_rfl hceil)
    convert hh using 1 <;> dsimp only [L] <;> ring
  apply (le_div_iff₀ hrootS).mpr
  calc
    g*Real.sqrt (s+L) ≤ ((2/5+(3/2)/Real.sqrt L)*(t : ℝ))*Real.sqrt (s+L) :=
      mul_le_mul_of_nonneg_right hg hrootS.le
    _ = ((2/5+(3/2)/Real.sqrt L)*Real.sqrt (s+L))*(t : ℝ) := by ring
    _ ≤ 3*(t : ℝ) := mul_le_mul_of_nonneg_right hcoef (by positivity)

end SymmetricSubgroupAsymptotics.OrderSixJointCoarseCeilingNumerics
