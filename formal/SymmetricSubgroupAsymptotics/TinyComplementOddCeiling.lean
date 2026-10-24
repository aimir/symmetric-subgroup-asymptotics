import SymmetricSubgroupAsymptotics.TinyComplementOddMargins
import SymmetricSubgroupAsymptotics.SmallPrimaryZeroMatchingCeiling

/-! Ceiling normalization for the uniform higher-dimensional tiny odd
interval. The input is the SAME joint single-divisor cost, not a scalar
conclusion that it already fits. The actual original installer supplies
all coefficient, degree and entropy hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyComplementOddCeiling

theorem aggregate_le (M d t : ℕ) (hM : 5 ≤ M) (hd : 4 ≤ d) (hMt : M ≤ t)
    (m C u g : ℝ) (hm0 : 0 ≤ m) (hmA : m ≤ (d : ℝ)-2) (hmC : m ≤ C)
    (hC : C ≤ (d : ℝ)^2-2) (hu : u ≤ 1/2)
    (hentropy : Real.logb 2 (t : ℝ) ≤ 10)
    (hcost : g ≤ (t : ℝ)*(m*u+(C-m)/(M : ℝ))+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  have hMR : (5 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hMtR : (M : ℝ) ≤ t := by exact_mod_cast hMt
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hM0 hMtR
  have hL : 2 ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 4) (by linarith only [hMR,hMtR] : (4 : ℝ) ≤ t)
    have heq : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      norm_num
    simpa only [heq,L] using hh
  have hL0 : 0 < L := by linarith only [hL]
  have hscaled := TinyComplementOddMargins.higher_envelope_le d hd (M : ℝ) m C u L
    hMR hm0 hmA hmC hC hu hL hentropy
  have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ (d : ℝ)+L)]
    congr 1
    field_simp [hL0.ne'] <;> ring
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le (Real.sqrt_nonneg _))).le
  have hunit : (1 : ℝ) ≤ (t : ℝ)/(M : ℝ) :=
    (le_div_iff₀ hM0).mpr (by simpa only [one_mul] using hMtR)
  have hg : g ≤ (t : ℝ)*(m*u+(C-m)/(M : ℝ))+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M : ℝ) := by
    change g ≤ (t : ℝ)*(m*u+(C-m)/(M : ℝ))+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
  have hscaled' : (m*u+(C-m+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    rw [hratio]
    exact hscaled
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*(m*u+(C-m)/(M : ℝ))+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M : ℝ))*Real.sqrt ((d : ℝ)+L) :=
      mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*((m*u+(C-m+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled' ht0.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _


end SymmetricSubgroupAsymptotics.TinyComplementOddCeiling
