import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import Mathlib.Tactic.IntervalCases

/-! Two small scalar seed bands, not finite group or action rows.
The top bracket is shared by all local sizes. The two target brackets
are uniform over local sizes 5..6 and 7..9. All witnesses are integral
power/square inequalities at fixed denominator64 (largest exponent453). -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonaffineTinyPairSmallTopOrdinaryCertificates
open IntegerLogSquareRootCeilingCertificate

private def bandLower (b : ℕ) : ℕ := if b = 2 then 5 else 7
private def bandUpper (b : ℕ) : ℕ := if b = 2 then 6 else 9
private def lowerLog : ℕ → ℕ
  | 2 => 64 | 3 => 101 | 4 => 128 | 5 => 148 | 6 => 165 | 7 => 179 | 8 => 192
  | 9 => 202 | 10 => 212 | 11 => 221 | 12 => 229 | 13 => 236 | 14 => 243 | _ => 250
private def topCut : ℕ → ℕ
  | 2 => 2 | 3 => 3 | 4 => 3 | 5 => 4 | 6 => 4 | 7 => 5 | 8 => 5
  | 9 => 6 | 10 => 6 | 11 => 6 | 12 => 7 | 13 => 7 | 14 => 8 | _ => 8
private def upperLog (b t : ℕ) : ℕ := if b = 2 then
  match t with
  | 2 => 230 | 3 => 267 | 4 => 294 | 5 => 315 | 6 => 331 | 7 => 346 | 8 => 358
  | 9 => 369 | 10 => 379 | 11 => 387 | 12 => 395 | 13 => 403 | 14 => 410 | _ => 416
  else match t with
  | 2 => 267 | 3 => 305 | 4 => 331 | 5 => 352 | 6 => 369 | 7 => 383 | 8 => 395
  | 9 => 406 | 10 => 416 | 11 => 425 | 12 => 433 | 13 => 440 | 14 => 447 | _ => 453
private def seedCut (b t : ℕ) : ℕ := 2+(b*t+1)/2+topCut t

private theorem top_power (t : ℕ) (ht2 : 2 ≤ t) (ht15 : t ≤ 15) :
    2^(lowerLog t) ≤ t^64 := by
  interval_cases t <;> decide +kernel
private theorem top_square (t : ℕ) (ht2 : 2 ≤ t) (ht15 : t ≤ 15) :
    64*t^2 ≤ lowerLog t*(topCut t)^2 := by
  interval_cases t <;> decide +kernel
private theorem target_power (b t : ℕ) (hb : b = 2 ∨ b = 3)
    (ht2 : 2 ≤ t) (ht15 : t ≤ 15) :
    (bandUpper b*t)^64 ≤ 2^(upperLog b t) := by
  rcases hb with rfl | rfl <;> interval_cases t <;> decide +kernel
private theorem target_square (b t : ℕ) (hb : b = 2 ∨ b = 3)
    (ht2 : 2 ≤ t) (ht15 : t ≤ 15) :
    (seedCut b t-1)^2*upperLog b t < 64*(bandLower b*t)^2 := by
  rcases hb with rfl | rfl <;> interval_cases t <;> decide +kernel

private theorem small_top_bound (r t b g : ℕ) (hb : b = 2 ∨ b = 3)
    (hrlo : bandLower b ≤ r) (hrhi : r ≤ bandUpper b)
    (ht2 : 2 ≤ t) (ht15 : t ≤ 15)
    (hcost : (g : ℝ) ≤ 2+(b : ℝ)*(t : ℝ)/2+traceyPermutationGeneratorCeiling t) :
    g ≤ traceyPermutationGeneratorCeiling (r*t) := by
  have hlow : 0 < lowerLog t := by interval_cases t <;> decide
  have htop : traceyPermutationGeneratorCeiling t ≤ topCut t :=
    ceil_le_of_square t 64 (lowerLog t) (topCut t) (by omega) (by decide) hlow
      (top_power t ht2 ht15) (top_square t ht2 ht15)
  have hhalf : b*t ≤ 2*((b*t+1)/2) := by omega
  have hhalfR : (b : ℝ)*(t : ℝ)/2 ≤ (((b*t+1)/2 : ℕ) : ℝ) := by
    have hh : (b : ℝ)*(t : ℝ) ≤ 2*(((b*t+1)/2 : ℕ) : ℝ) := by exact_mod_cast hhalf
    linarith only [hh]
  have htopR : (traceyPermutationGeneratorCeiling t : ℝ) ≤ topCut t := by exact_mod_cast htop
  have hg : g ≤ seedCut b t := by
    have hh : (g : ℝ) ≤ (seedCut b t : ℝ) := by
      simp only [seedCut,Nat.cast_add,Nat.cast_ofNat]
      linarith only [hcost,hhalfR,htopR]
    exact_mod_cast hh
  have hpow : (r*t)^64 ≤ 2^(upperLog b t) :=
    (Nat.pow_le_pow_left (Nat.mul_le_mul_right t hrhi) 64).trans
      (target_power b t hb ht2 ht15)
  have hsquare : (seedCut b t-1)^2*upperLog b t < 64*(r*t)^2 :=
    (target_square b t hb ht2 ht15).trans_le
      (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.mul_le_mul_right t hrlo) 2))
  have hr5 : 5 ≤ r := by
    rcases hb with rfl | rfl <;> simp only [bandLower,ite_true,show (3 : ℕ) ≠ 2 by decide,ite_false] at hrlo <;> omega
  have hdegree : 2 ≤ r*t := (by decide : 2 ≤ 5*2).trans (Nat.mul_le_mul hr5 ht2)
  exact hg.trans (le_ceil_of_square (r*t) 64 (upperLog b t) (seedCut b t)
    hdegree (by decide) (by dsimp only [seedCut]; omega) hpow hsquare)

theorem five_six_rank_le (r t g : ℕ) (hr5 : 5 ≤ r) (hr6 : r ≤ 6)
    (ht2 : 2 ≤ t) (ht15 : t ≤ 15)
    (hcost : (g : ℝ) ≤ 2+(t : ℝ)+traceyPermutationGeneratorCeiling t) :
    g ≤ traceyPermutationGeneratorCeiling (r*t) := by
  apply small_top_bound r t 2 g (Or.inl rfl) (by simpa only [bandLower,ite_true] using hr5)
    (by simpa only [bandUpper,ite_true] using hr6) ht2 ht15
  nlinarith only [hcost]

theorem seven_nine_rank_le (r t g : ℕ) (hr7 : 7 ≤ r) (hr9 : r ≤ 9)
    (ht2 : 2 ≤ t) (ht15 : t ≤ 15)
    (hcost : (g : ℝ) ≤ 2+3*(t : ℝ)/2+traceyPermutationGeneratorCeiling t) :
    g ≤ traceyPermutationGeneratorCeiling (r*t) := by
  apply small_top_bound r t 3 g (Or.inr rfl)
    (by simpa only [bandLower,show (3 : ℕ) ≠ 2 by decide,ite_false] using hr7)
    (by simpa only [bandUpper,show (3 : ℕ) ≠ 2 by decide,ite_false] using hr9) ht2 ht15
  exact hcost

end SymmetricSubgroupAsymptotics.NonaffineTinyPairSmallTopOrdinaryCertificates
