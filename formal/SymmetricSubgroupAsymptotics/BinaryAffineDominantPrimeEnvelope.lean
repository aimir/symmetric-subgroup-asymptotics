import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeRemainderNumerics
import SymmetricSubgroupAsymptotics.CappedInverseSqrtEndpointBound
import SymmetricSubgroupAsymptotics.ActualDivisorWeightRateBounds

/-! The full scalar dominant-prime envelope, including the actual top
ratio and natural-ceiling error, for dimensions one through six and a
large literal primary exponent. Its coefficients are only order
multiplicities; binding them to the original action is a separate step. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeEnvelope
open BinaryAffineDominantPrimeSwitchNumerics BinaryAffineDominantPrimeRemainderNumerics

theorem envelope_le (q a d : ℕ) (hq : q.Prime) (ha : 512 ≤ a)
    (hd1 : 1 ≤ d) (hd6 : d ≤ 6) (C m v : ℝ)
    (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ ((d+d*(d-1)/2 : ℕ) : ℝ))
    (hv : 0 < v) (hvM : v ≤ (q : ℝ)^a) :
    (m*min (rate q a) (1/v)+(C-m+1)/(q : ℝ)^a)*
        Real.sqrt ((d : ℝ)+(a : ℝ)*Real.logb 2 (q : ℝ)+8*v) +
      Real.sqrt (1+(d : ℝ)/((a : ℝ)*Real.logb 2 (q : ℝ))) ≤ (2 : ℝ)^d := by
  let M : ℕ := q^a
  let u := rate q a
  let c := (d : ℝ)+(a : ℝ)*Real.logb 2 (q : ℝ)
  let b := (C-m+1)/(M : ℝ)
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
  have haR : (512 : ℝ) ≤ a := by exact_mod_cast ha
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hden : 0 < 3*((q : ℝ)-1)*a :=
    mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hu : 0 < u := Real.sqrt_pos.mpr (div_pos (by norm_num) hden)
  have hlog1 : (1 : ℝ) ≤ Real.logb 2 (q : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) hqR
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hL : (512 : ℝ) ≤ (a : ℝ)*Real.logb 2 (q : ℝ) := by
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
  have hswitchError := other_endpoint_le M hM (d : ℝ) (C-m+1) (1/u)
    hd0 hdR6 (by linarith) (by linarith) (one_div_pos.mpr hu).le hsM
  rw [hlogM] at hswitchError
  have hswitchPrimary : u*Real.sqrt (c+8*(1/u)) ≤ 99/100 := by
    simpa only [u,c,div_eq_mul_inv,one_mul] using
      primary_switch_le q a hq.two_le ha (d : ℝ) hd0 hdR6
  have hswitch : (m*u+b)*Real.sqrt (c+8*(1/u)) ≤ (99/100)*m+1/1024 := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hswitchPrimary hm0) hswitchError
    dsimp only [b,c] at hh ⊢
    nlinarith only [hh]
  have hrightError := other_endpoint_le M hM (d : ℝ) (C+1) (M : ℝ)
    hd0 hdR6 (by linarith) (by linarith) hM0.le le_rfl
  rw [hlogM] at hrightError
  have hright : (m/(M : ℝ)+b)*Real.sqrt (c+8*(M : ℝ)) ≤ (99/100)*m+1/1024 := by
    have heq : m/(M : ℝ)+b = (C+1)/(M : ℝ) := by dsimp only [b]; ring
    rw [heq]
    exact hrightError.trans (by nlinarith only [hm0])
  have hcap := CappedInverseSqrtEndpointBound.le_switch_or_right
    m u b c 8 (M : ℝ) v hm0 hu hb hc (by norm_num) hv
      (by simpa only [M,Nat.cast_pow] using hvM)
  have hcap' : CappedInverseSqrtEndpointBound.capped m u b c 8 v ≤
      (99/100)*m+1/1024 := hcap.trans (max_le hswitch hright)
  have htop := top_ratio_le (d : ℝ) ((a : ℝ)*Real.logb 2 (q : ℝ)) hd0 hL
  have hsum := add_le_add hcap' htop
  have hmargin := quadratic_margin d hd1
  have hm := mul_le_mul_of_nonneg_left hmA (by norm_num : (0 : ℝ) ≤ 99/100)
  simp only [CappedInverseSqrtEndpointBound.capped,u,b,c,M,Nat.cast_pow] at hsum
  nlinarith only [hsum,hmargin,hm]

end SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeEnvelope
