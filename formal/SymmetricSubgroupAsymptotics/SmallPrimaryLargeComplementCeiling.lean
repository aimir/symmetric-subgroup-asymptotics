import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementMargins
import SymmetricSubgroupAsymptotics.SmallPrimaryZeroMatchingCeiling

/-! A uniform ceiling bridge for the actual two-divisor total rate C/v.
The coprime dominant and complementary primary powers give v^2<=t;
this retains the genuine natural-ceiling error. No scalar fitting or
assumed current-degree generator bound is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementCeiling

theorem aggregate_le (v d t : ℕ) (hv : 5 ≤ v) (hd : 4 ≤ d) (hproduct : v^2 ≤ t)
    (C g : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hentropy : Real.logb 2 (t : ℝ) ≤ 6+(3/2)*(v : ℝ))
    (hcost : g ≤ (t : ℝ)*C/(v : ℝ)+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  have hvR : (5 : ℝ) ≤ v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith only [hvR]
  have ht25 : 25 ≤ t := by nlinarith only [hproduct,hv]
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hproductR : (v : ℝ)^2 ≤ t := by exact_mod_cast hproduct
  have hL : 4 ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 16) (by exact_mod_cast (show 16 ≤ t by omega) : (16 : ℝ) ≤ t)
    have heq : Real.logb 2 (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 2^4 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      norm_num
    simpa only [heq,L] using hh
  have hL0 : 0 < L := by linarith only [hL]
  have hscaled := SmallPrimaryLargeComplementMargins.envelope_le (v : ℝ) d hvR hd C L hC0 hC hL hentropy
  have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ (d : ℝ)+L)]
    congr 1
    field_simp [hL0.ne'] <;> ring
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le (Real.sqrt_nonneg _))).le
  have hunit : (1 : ℝ) ≤ (t : ℝ)/(v : ℝ)^2 :=
    (le_div_iff₀ (pow_pos hv0 2)).mpr (by simpa only [one_mul] using hproductR)
  have hg : g ≤ (t : ℝ)*C/(v : ℝ)+(t : ℝ)/Real.sqrt L+(t : ℝ)/(v : ℝ)^2 := by
    change g ≤ (t : ℝ)*C/(v : ℝ)+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
  have hscaled' : (C/(v : ℝ)+1/(v : ℝ)^2)*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    rw [hratio]
    exact hscaled
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*C/(v : ℝ)+(t : ℝ)/Real.sqrt L+(t : ℝ)/(v : ℝ)^2)*Real.sqrt ((d : ℝ)+L) :=
      mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*((C/(v : ℝ)+1/(v : ℝ)^2)*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled' ht0.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _


end SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementCeiling
