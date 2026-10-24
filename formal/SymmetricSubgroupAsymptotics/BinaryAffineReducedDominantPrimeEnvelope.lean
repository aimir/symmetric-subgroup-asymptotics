import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeEnvelope
import SymmetricSubgroupAsymptotics.BinaryAffineReducedDominantPrimeNumerics

/-! The exponent128 scalar envelope with sharper17/4 entropy. The SAME
order coefficients, exact top ratio and natural-ceiling error are all
retained; no remaining finite window is declared paid by assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineReducedDominantPrimeEnvelope
open BinaryAffineDominantPrimeSwitchNumerics BinaryAffineDominantPrimeRemainderNumerics

theorem envelope_le (q a d : ℕ) (hq : q.Prime) (ha : 128 ≤ a)
    (hd1 : 1 ≤ d) (hd6 : d ≤ 6) (C m v : ℝ)
    (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ ((d+d*(d-1)/2 : ℕ) : ℝ))
    (hv : 0 < v) (hvM : v ≤ (q : ℝ)^a) :
    (m*min (rate q a) (1/v)+(C-m+1)/(q : ℝ)^a)*
        Real.sqrt ((d : ℝ)+(a : ℝ)*Real.logb 2 (q : ℝ)+(17/4)*v) +
      Real.sqrt (1+(d : ℝ)/((a : ℝ)*Real.logb 2 (q : ℝ))) ≤ (2 : ℝ)^d := by
  let M : ℕ := q^a
  let u := rate q a
  let c := (d : ℝ)+(a : ℝ)*Real.logb 2 (q : ℝ)
  let b := (C-m+1)/(M : ℝ)
  let R := ((d : ℝ)+379)/384
  have hM : 2^40 ≤ M :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 40 ≤ a)).trans
      (Nat.pow_le_pow_left hq.two_le a)
  have hMR : (1099511627776 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hdR6 : (d : ℝ) ≤ 6 := by exact_mod_cast hd6
  have hdSq : (d : ℝ)^2 ≤ (6 : ℝ)^2 :=
    (sq_le_sq₀ hd0 (by norm_num : (0 : ℝ) ≤ 6)).mpr hdR6
  have hC36 : C ≤ 36 := by nlinarith only [hC,hdSq]
  have hC0 : 0 ≤ C := hm0.trans hmC
  have haR : (128 : ℝ) ≤ a := by exact_mod_cast ha
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hden : 0 < 3*((q : ℝ)-1)*a :=
    mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hu : 0 < u := Real.sqrt_pos.mpr (div_pos (by norm_num) hden)
  have hR0 : 0 ≤ R := by positivity
  have hlog1 : (1 : ℝ) ≤ Real.logb 2 (q : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) hqR
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hL : (128 : ℝ) ≤ (a : ℝ)*Real.logb 2 (q : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlog1 (show (0 : ℝ) ≤ a by positivity)
    nlinarith only [hh,haR]
  have hc : 0 ≤ c := by dsimp only [c]; linarith
  have hb : 0 ≤ b := div_nonneg (by linarith) hM0.le
  have hlogM : Real.logb 2 (M : ℝ) = (a : ℝ)*Real.logb 2 (q : ℝ) := by
    simp only [M,Nat.cast_pow,Real.logb_pow]
  have hunit : 1 ≤ (M : ℝ)*u := by
    have hh := ActualDivisorWeightRateBounds.one_le_divisorRate M q a q
      (by omega : 2 ≤ M) hq (by omega : 1 ≤ a) (dvd_refl _)
    simpa only [ActualWreathChiefDivisorWeights.divisorRate,if_pos rfl,rate,u] using hh
  have hsM : 1/u ≤ (M : ℝ) :=
    (div_le_iff₀ hu).mpr (by simpa only [one_mul,mul_comm] using hunit)
  have herror (B x : ℝ) (hB0 : 0 ≤ B) (hB37 : B ≤ 37) (hx0 : 0 ≤ x) (hxM : x ≤ M) :
      (B/(M : ℝ))*Real.sqrt (c+(17/4)*x) ≤ 1/1024 := by
    have hh := other_endpoint_le M hM (d : ℝ) B x hd0 hdR6 hB0 hB37 hx0 hxM
    rw [hlogM] at hh
    have hrad : c+(17/4)*x ≤ c+8*x := by nlinarith only [hx0]
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad)
      (div_nonneg hB0 hM0.le)).trans hh
  have hswitchError := herror (C-m+1) (1/u) (by linarith) (by linarith)
    (one_div_pos.mpr hu).le hsM
  have hswitchPrimary : u*Real.sqrt (c+(17/4)*(1/u)) ≤ R := by
    simpa only [u,c,R,div_eq_mul_inv,one_mul] using
      BinaryAffineReducedDominantPrimeNumerics.primary_switch_le q a hq.two_le ha (d : ℝ) hd0
  have hswitch : (m*u+b)*Real.sqrt (c+(17/4)*(1/u)) ≤ m*R+1/1024 := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hswitchPrimary hm0) hswitchError
    dsimp only [b] at hh ⊢
    nlinarith only [hh]
  have hrightError := herror (C+1) (M : ℝ) (by linarith) (by linarith) hM0.le le_rfl
  have hright : (m/(M : ℝ)+b)*Real.sqrt (c+(17/4)*(M : ℝ)) ≤ m*R+1/1024 := by
    have heq : m/(M : ℝ)+b = (C+1)/(M : ℝ) := by dsimp only [b]; ring
    rw [heq]
    exact hrightError.trans (by nlinarith only [mul_nonneg hm0 hR0])
  have hcap := CappedInverseSqrtEndpointBound.le_switch_or_right
    m u b c (17/4) (M : ℝ) v hm0 hu hb hc (by norm_num) hv
      (by simpa only [M,Nat.cast_pow] using hvM)
  have hcap' : CappedInverseSqrtEndpointBound.capped m u b c (17/4) v ≤ m*R+1/1024 :=
    hcap.trans (max_le hswitch hright)
  have htop : Real.sqrt (1+(d : ℝ)/((a : ℝ)*Real.logb 2 (q : ℝ))) ≤ 1+(d : ℝ)/256 := by
    have hh := div_le_div_of_nonneg_left hd0 (by norm_num : (0 : ℝ) < 128) hL
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_nonneg (d : ℝ)]
  have hsum := add_le_add hcap' htop
  have hmargin := BinaryAffineReducedDominantPrimeNumerics.aggregate_margin d hd1
  have hm := mul_le_mul_of_nonneg_right hmA hR0
  simp only [CappedInverseSqrtEndpointBound.capped,u,b,c,M,Nat.cast_pow] at hsum
  dsimp only [R] at hsum hm
  nlinarith only [hsum,hmargin,hm]

end SymmetricSubgroupAsymptotics.BinaryAffineReducedDominantPrimeEnvelope
