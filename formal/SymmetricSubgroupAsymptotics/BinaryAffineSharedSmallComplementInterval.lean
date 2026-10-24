import SymmetricSubgroupAsymptotics.OddSmallComplementCeilingAggregation
import SymmetricSubgroupAsymptotics.CentralBinomialNormalizedAntitone
import SymmetricSubgroupAsymptotics.ActualWreathChooseDivisorCapacity

/-! A shared-head scalar interval with an actual top ceiling. The
coefficients are the proved zero/nonzero odd-kernel costs, and the exact
choose rate is retained. No action, exponent, or group census is used.
The logarithmic interval is installed from the actual point count in a
separate original-action consumer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineSharedSmallComplementInterval
open ActualWreathChooseDivisorCapacity

theorem shared_choose_coefficient_le (a : ℕ) (ha : 6 ≤ a) :
    max (2 * primaryRate 2 a)
      ((1 / 2 : ℝ) + primaryRate 2 a + 1 / (2 : ℝ) ^ a) ≤ 53 / 64 := by
  have hu : primaryRate 2 a ≤ 5 / 16 := by
    have hh : primaryRate 2 a ≤ primaryRate 2 6 := by
      simpa only [primaryRate,show (2 : ℕ) - 1 = 1 by decide,Nat.mul_one] using
        CentralBinomialNormalizedAntitone.normalized_antitone ha
    have h6 : primaryRate 2 6 = 5 / 16 := by
      norm_num [primaryRate,show Nat.choose 6 3 = 20 by decide]
    exact hh.trans_eq h6
  have hpow : (64 : ℝ) ≤ (2 : ℝ) ^ a := by
    have hn : (2 : ℕ) ^ 6 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) ha
    exact_mod_cast hn
  have hi : (1 : ℝ) / (2 : ℝ) ^ a ≤ 1 / 64 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow
  exact max_le (by linarith) (by linarith)

theorem scaled_budget_le (L t : ℝ) (hL : 7 ≤ L) (hupper : L ≤ 43 / 5) (ht : 192 ≤ t) :
    (53 / 64 : ℝ) * Real.sqrt (2 + L) + Real.sqrt ((2 + L) / L) +
      Real.sqrt (2 + L) / t ≤ 4 := by
  have hL0 : 0 < L := by linarith
  have ht0 : 0 < t := by linarith
  have hA : 0 ≤ 2 + L := by linarith
  have hroot : Real.sqrt (2 + L) ≤ 33 / 10 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 33 / 10)).mp
    rw [Real.sq_sqrt hA]
    linarith
  have hfrac : (2 + L) / L ≤ (64 / 49 : ℝ) :=
    (div_le_iff₀ hL0).mpr (by linarith)
  have hfrac0 : 0 ≤ (2 + L) / L := div_nonneg hA hL0.le
  have hratio : Real.sqrt ((2 + L) / L) ≤ 8 / 7 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8 / 7)).mp
    rw [Real.sq_sqrt hfrac0]
    nlinarith only [hfrac]
  have herror : Real.sqrt (2 + L) / t ≤ (11 / 640 : ℝ) :=
    (div_le_iff₀ ht0).mpr (by nlinarith only [hroot,ht])
  have hmain := mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 53 / 64)
  linarith only [hmain,hratio,herror]

theorem aggregate_le (t : ℕ) (ht : 192 ≤ t)
    (hlower : 7 ≤ Real.logb 2 (t : ℝ)) (hupper : Real.logb 2 (t : ℝ) ≤ 43 / 5)
    (g : ℝ) (hcost : g ≤ (53 / 64 : ℝ) * t +
      (⌈(t : ℝ) / Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ 4 * (t : ℝ) / Real.sqrt (2 + Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  have htR : (192 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hlower]
  have hA : 0 ≤ 2 + L := by linarith
  have hs : 0 < Real.sqrt (2 + L) := Real.sqrt_pos.mpr (by linarith)
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hratio : Real.sqrt (2 + L) / Real.sqrt L = Real.sqrt ((2 + L) / L) := by
    rw [← Real.sqrt_div hA]
  have hscaled : (53 / 64 : ℝ) * Real.sqrt (2 + L) +
      Real.sqrt (2 + L) / Real.sqrt L + Real.sqrt (2 + L) / t ≤ 4 := by
    rw [hratio]
    exact scaled_budget_le L t hlower hupper htR
  have hceil : (⌈(t : ℝ) / Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ) / Real.sqrt L + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le hsL.le)).le
  have hg : g ≤ (53 / 64 : ℝ) * t + (t : ℝ) / Real.sqrt L + 1 := by
    change g ≤ (53 / 64 : ℝ) * t + (⌈(t : ℝ) / Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil]
  change g ≤ 4 * (t : ℝ) / Real.sqrt (2 + L)
  apply (le_div_iff₀ hs).mpr
  calc
    g * Real.sqrt (2 + L) ≤
        ((53 / 64 : ℝ) * t + (t : ℝ) / Real.sqrt L + 1) * Real.sqrt (2 + L) :=
      mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ) * ((53 / 64 : ℝ) * Real.sqrt (2 + L) +
        Real.sqrt (2 + L) / Real.sqrt L + Real.sqrt (2 + L) / t) := by
      field_simp [ht0.ne',hsL.ne']
    _ ≤ (t : ℝ) * 4 := mul_le_mul_of_nonneg_left hscaled ht0.le
    _ = 4 * (t : ℝ) := mul_comm _ _

end SymmetricSubgroupAsymptotics.BinaryAffineSharedSmallComplementInterval
