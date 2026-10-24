import SymmetricSubgroupAsymptotics.OddAffineTameOrderTailNumerics
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorNumerics

/-! Two-regime tame-affine ceiling aggregation, with one literal binary
window for the local degree. The order coefficient is derived later from
the actual affine action. All numerical regimes here are proved uniformly
in k>=7; no scalar-fit field or top-degree enumeration is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OddAffineTameOrderRealTail

def tameCost (k : ℕ) : ℝ := (2/3)*((k : ℝ)+1)*((k : ℝ)+2)

private theorem four_pow_eq_two_pow_square (k : ℕ) :
    (4 : ℝ)^k = ((2 : ℝ)^k)^2 := by
  calc
    (4 : ℝ)^k = ((2 : ℝ)^2)^k := by norm_num
    _ = (2 : ℝ)^(2*k) := (pow_mul _ _ _).symm
    _ = (2 : ℝ)^(k*2) := by rw [Nat.mul_comm]
    _ = ((2 : ℝ)^k)^2 := pow_mul _ _ _

theorem aggregate_le (k : ℕ) (hk : 7 ≤ k) (s R t g : ℝ)
    (hs0 : 0 ≤ s) (hsK : s ≤ (k : ℝ)+1) (hR : (2 : ℝ)^k ≤ R) (ht : 2 ≤ t)
    (hhalf : g ≤ tameCost k*t/2+(⌈t/Real.sqrt (Real.logb 2 t)⌉₊ : ℝ))
    (hlog : g ≤ 2*tameCost k*t/Real.sqrt (Real.logb 2 t)+
      (⌈t/Real.sqrt (Real.logb 2 t)⌉₊ : ℝ)) :
    g ≤ R*t/Real.sqrt (s+Real.logb 2 t) := by
  let L := Real.logb 2 t
  let K : ℝ := (k : ℝ)+1
  let B := tameCost k
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B,tameCost]; positivity
  have hR0 : 0 ≤ R := le_trans (by positivity : (0 : ℝ) ≤ (2 : ℝ)^k) hR
  have hRpow : ((2 : ℝ)^k)^2 ≤ R^2 :=
    (sq_le_sq₀ (by positivity) hR0).mpr hR
  have hL1 : 1 ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) ht
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hL : 0 < L := by linarith only [hL1]
  have hrootL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hrootS : 0 < Real.sqrt (s+L) := Real.sqrt_pos.mpr (by linarith only [hs0,hL])
  have hLsq : (Real.sqrt L)^2 = L := Real.sq_sqrt hL.le
  have hSsq : (Real.sqrt (s+L))^2 = s+L := Real.sq_sqrt (by linarith only [hs0,hL])
  have hs1 : 1 ≤ Real.sqrt L := by
    have hh := Real.sqrt_le_sqrt hL1
    simpa only [Real.sqrt_one] using hh
  have hsle : Real.sqrt L ≤ t :=
    (Real.sqrt_le_iff).mpr ⟨ht0,LargeOrbitGeneratorNumerics.logb_le_square ht⟩
  have hunit : (1 : ℝ) ≤ t/Real.sqrt L := (le_div_iff₀ hrootL).mpr (by simpa using hsle)
  have hceil : (⌈t/Real.sqrt L⌉₊ : ℝ) ≤ t/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0 hrootL.le)).le
  change g ≤ B*t/2+(⌈t/Real.sqrt L⌉₊ : ℝ) at hhalf
  change g ≤ 2*B*t/Real.sqrt L+(⌈t/Real.sqrt L⌉₊ : ℝ) at hlog
  change g ≤ R*t/Real.sqrt (s+L)
  by_cases hsmall : L ≤ 2*K
  · have hbudget : 3*K*(B/2+2)^2 ≤ ((2 : ℝ)^k)^2 := by
      have hn := OddAffineTameOrderTailNumerics.small_log_budget k hk
      have hh0 : ((k : ℝ)+1)*(((k : ℝ)+1)*((k : ℝ)+2)+6)^2 ≤ 3*(4 : ℝ)^k := by
        exact_mod_cast hn
      have hh : K*(K*(K+1)+6)^2 ≤ 3*(4 : ℝ)^k := by
        dsimp only [K]
        convert hh0 using 1 <;> ring
      rw [four_pow_eq_two_pow_square] at hh
      calc
        3*K*(B/2+2)^2 = (K*(K*(K+1)+6)^2)/3 := by
          dsimp only [B,tameCost,K]
          ring
        _ ≤ ((2 : ℝ)^k)^2 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
          (by nlinarith only [hh])
    have hcoefSq : ((B/2+2)*Real.sqrt (s+L))^2 ≤ R^2 := by
      calc
        _ = (B/2+2)^2*(s+L) := by rw [mul_pow,hSsq]
        _ ≤ (B/2+2)^2*(3*K) :=
          mul_le_mul_of_nonneg_left (by linarith only [hsK,hsmall]) (sq_nonneg _)
        _ = 3*K*(B/2+2)^2 := by ring
        _ ≤ ((2 : ℝ)^k)^2 := hbudget
        _ ≤ R^2 := hRpow
    have hcoef : (B/2+2)*Real.sqrt (s+L) ≤ R :=
      (sq_le_sq₀ (mul_nonneg (by positivity) hrootS.le) hR0).mp hcoefSq
    have hdiv : t/Real.sqrt L ≤ t := (div_le_iff₀ hrootL).mpr
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 ht0)
    have hg : g ≤ (B/2+2)*t := by nlinarith only [hhalf,hceil,hdiv,ht]
    apply (le_div_iff₀ hrootS).mpr
    calc
      g*Real.sqrt (s+L) ≤ ((B/2+2)*t)*Real.sqrt (s+L) :=
        mul_le_mul_of_nonneg_right hg hrootS.le
      _ = ((B/2+2)*Real.sqrt (s+L))*t := by ring
      _ ≤ R*t := mul_le_mul_of_nonneg_right hcoef ht0
  · have hlarge : 2*K ≤ L := by linarith only [hsmall]
    have hbudget : (3/2)*(2*B+2)^2 ≤ ((2 : ℝ)^k)^2 := by
      have hn := OddAffineTameOrderTailNumerics.large_log_budget k hk
      have hh0 : 2*(2*((k : ℝ)+1)*((k : ℝ)+2)+3)^2 ≤ 3*(4 : ℝ)^k := by
        exact_mod_cast hn
      have hh : 2*(2*K*(K+1)+3)^2 ≤ 3*(4 : ℝ)^k := by
        dsimp only [K]
        convert hh0 using 1 <;> ring
      rw [four_pow_eq_two_pow_square] at hh
      calc
        (3/2)*(2*B+2)^2 = (2*(2*K*(K+1)+3)^2)/3 := by
          dsimp only [B,tameCost,K]
          ring
        _ ≤ ((2 : ℝ)^k)^2 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
          (by nlinarith only [hh])
    have hcoefSq : ((2*B+2)*Real.sqrt (s+L))^2 ≤ (R*Real.sqrt L)^2 := by
      calc
        _ = (2*B+2)^2*(s+L) := by rw [mul_pow,hSsq]
        _ ≤ (2*B+2)^2*((3/2)*L) :=
          mul_le_mul_of_nonneg_left (by linarith only [hsK,hlarge]) (sq_nonneg _)
        _ = ((3/2)*(2*B+2)^2)*L := by ring
        _ ≤ R^2*L := mul_le_mul_of_nonneg_right (hbudget.trans hRpow) hL.le
        _ = (R*Real.sqrt L)^2 := by rw [mul_pow,hLsq]
    have hcoef : (2*B+2)*Real.sqrt (s+L) ≤ R*Real.sqrt L :=
      (sq_le_sq₀ (mul_nonneg (by positivity) hrootS.le) (mul_nonneg hR0 hrootL.le)).mp hcoefSq
    have hunit2 : t/Real.sqrt L+1 ≤ 2*(t/Real.sqrt L) := by linarith only [hunit]
    have hg : g ≤ (2*B+2)*t/Real.sqrt L := by
      calc
        g ≤ 2*B*t/Real.sqrt L+(⌈t/Real.sqrt L⌉₊ : ℝ) := hlog
        _ ≤ 2*B*t/Real.sqrt L+(t/Real.sqrt L+1) := add_le_add le_rfl hceil
        _ ≤ 2*B*t/Real.sqrt L+2*(t/Real.sqrt L) := add_le_add le_rfl hunit2
        _ = (2*B+2)*t/Real.sqrt L := by ring
    apply (le_div_iff₀ hrootS).mpr
    calc
      g*Real.sqrt (s+L) ≤ ((2*B+2)*t/Real.sqrt L)*Real.sqrt (s+L) :=
        mul_le_mul_of_nonneg_right hg hrootS.le
      _ = ((2*B+2)*Real.sqrt (s+L))*t/Real.sqrt L := by ring
      _ ≤ (R*Real.sqrt L)*t/Real.sqrt L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef ht0) hrootL.le
      _ = R*t := by rw [mul_right_comm,mul_div_cancel_right₀ _ hrootL.ne']

end SymmetricSubgroupAsymptotics.OddAffineTameOrderRealTail
