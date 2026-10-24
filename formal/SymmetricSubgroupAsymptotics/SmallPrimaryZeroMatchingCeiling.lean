import SymmetricSubgroupAsymptotics.SmallPrimaryZeroMatchingMargins
import SymmetricSubgroupAsymptotics.OddSmallComplementCeilingAggregation

/-! A uniform zero-matching ceiling step from bounded actual lcm
entropy. The natural ceiling error is retained as one extra primary
denominator charge. No fitting conclusion or top-degree census is an
input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryZeroMatchingCeiling
open SmallPrimaryZeroMatchingMargins

private theorem envelope_le (M d : ℕ) (hM : 11 ≤ M) (hd : 1 ≤ d)
    (C L : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hL : 3 ≤ L) (hentropy : L ≤ (3/2)*(M : ℝ)) :
    ((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
  have hMR : (11 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hroot : Real.sqrt ((d : ℝ)+L)/(M : ℝ) ≤ ((d : ℝ)+20)/55 :=
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt
      (add_le_add (le_rfl : (d : ℝ) ≤ d) hentropy)) hM0.le).trans
        (root_div_le M d hM hd)
  have hmain : ((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L) ≤
      ((d : ℝ)^2+1)*((d : ℝ)+20)/55 := by
    have hfirst := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ C+1 by linarith only [hC0])
    have hsecond := mul_le_mul_of_nonneg_right (add_le_add hC (le_rfl : (1 : ℝ) ≤ 1))
      (show 0 ≤ ((d : ℝ)+20)/55 by positivity)
    have hh := hfirst.trans hsecond
    convert hh using 1 <;> ring
  have htop : Real.sqrt (1+(d : ℝ)/L) ≤ 1+(d : ℝ)/6 := by
    have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ d by positivity)
      (by norm_num : (0 : ℝ) < 3) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_nonneg (d : ℝ)]
  calc
    ((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+Real.sqrt (1+(d : ℝ)/L) ≤ budget d := by
      dsimp only [budget]
      linarith only [hmain,htop]
    _ ≤ (2 : ℝ)^d := budget_le d hd

theorem aggregate_le (M d t : ℕ) (hM : 11 ≤ M) (hd : 1 ≤ d) (hMt : M ≤ t)
    (C g : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hentropy : Real.logb 2 (t : ℝ) ≤ (3/2)*(M : ℝ))
    (hcost : g ≤ (t : ℝ)*C/(M : ℝ)+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  have hMR : (11 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hMtR : (M : ℝ) ≤ t := by exact_mod_cast hMt
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hM0 hMtR
  have hL : 3 ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 8) (by linarith only [hMR,hMtR] : (8 : ℝ) ≤ t)
    have heq : Real.logb 2 (8 : ℝ) = 3 := by
      rw [show (8 : ℝ) = 2^3 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      norm_num
    simpa only [heq,L] using hh
  have hL0 : 0 < L := by linarith only [hL]
  have hscaled := envelope_le M d hM hd C L hC0 hC hL hentropy
  have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ (d : ℝ)+L)]
    congr 1
    field_simp [hL0.ne'] <;> ring
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le (Real.sqrt_nonneg _))).le
  have hunit : (1 : ℝ) ≤ (t : ℝ)/(M : ℝ) :=
    (le_div_iff₀ hM0).mpr (by simpa only [one_mul] using hMtR)
  have hg : g ≤ (t : ℝ)*C/(M : ℝ)+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M : ℝ) := by
    change g ≤ (t : ℝ)*C/(M : ℝ)+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
  have hscaled' : ((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    rw [hratio]
    exact hscaled
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*C/(M : ℝ)+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M : ℝ))*Real.sqrt ((d : ℝ)+L) :=
      mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*(((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled' ht0.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _

end SymmetricSubgroupAsymptotics.SmallPrimaryZeroMatchingCeiling
