import SymmetricSubgroupAsymptotics.MarkedC4ConstructedLargeOrbitMoment

/-! Cutoff numerics for the constructed large-orbit code. The selected
container is charged once. Its menu contributes O(b log(b+2)); the actual
relative tuple has length at most rate*b+1. Selecting rate before the cutoff
pays both the unmarked tuple and the single global C4-mark restriction.
All structural data are constructed; the only inputs are ordinary published
Proposition6.2 and the Pyber/Dixon statements in Theorem8.6. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ConstructedLargeOrbitCutoff
open ConstructedLargeOrbitMoment LargeOrbitOrdinaryGeneration
open SolubleContainerCount SolubleContainerOrder

theorem menuSize_le (b : ℕ) : menuSize b ≤ (b+2)^(15*b) := by
  unfold menuSize
  calc
    _ ≤ (b+2)^b * ((b+2)^(13*b) * (b+2)^b) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
        (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
          (Nat.pow_le_pow_left (by omega) _))
    _ = _ := by
      rw [← pow_add,← pow_add]
      congr 1
      omega

theorem menuSize_exp_bound (b : ℕ) :
    (menuSize b : ℝ) ≤ (2 : ℝ)^(boundedWordError 14 b 0) := by
  have he : boundedWordError 14 b 0 =
      Real.logb 2 ((b : ℝ)+2) * ((15*b : ℕ) : ℝ) := by
    unfold boundedWordError Real.logb
    push_cast
    ring
  rw [he,Real.rpow_mul (by norm_num : (0 : ℝ)≤2),
    Real.rpow_logb (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1) (by positivity),
    Real.rpow_natCast]
  exact_mod_cast menuSize_le b

theorem code_cost_le (rate : ℝ) (b r : ℕ) :
    ((menuSize b * 2^(2*b*tupleLength rate b) : ℕ) : ℝ) *
      (2 : ℝ)^(2*r*tupleLength rate b) ≤
    (2 : ℝ)^(boundedWordError 14 b 0 +
      2*((b : ℝ)+r)*tupleLength rate b) := by
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ (2 : ℝ)^(boundedWordError 14 b 0) *
        2^(2*b*tupleLength rate b) * 2^(2*r*tupleLength rate b) := by
      gcongr
      exact menuSize_exp_bound b
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_natCast,
        ← Real.rpow_add (by norm_num : (0 : ℝ)<2),
        ← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      congr 1
      push_cast
      ring

/-- The completed large-orbit reduction is uniform even without fixing an
r/b window: b→∞ pays the linear ceiling error for every r≥0. -/
theorem marked_bound
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hDixon : PublishedDixonOrder) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ᶠ b : ℕ in atTop, ∀ r : ℕ,
      solubleMarkedC4Moment b r ≤
        (2 : ℝ)^(δ*((b : ℝ)+r)^2) * OrbitCutoffFamilies.solubleCount C b r := by
  let rate : ℝ := δ/8
  have hrate : 0 < rate := by dsimp [rate]; positivity
  obtain ⟨C,hC,hfinite⟩ := exists_cutoff_moment_le h62 h86 hDixon rate hrate
  refine ⟨C,hC,?_⟩
  filter_upwards [boundedWordError_negligible (A := 14) (by norm_num)
      (δ/4) (by positivity) 0, eventually_ge_atTop (⌈8/δ⌉₊)] with b hmenu hb
  intro r
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hm : boundedWordError 14 b 0 ≤ (δ/4)*(b : ℝ)^2 := by
    simpa only [Nat.cast_zero,add_zero] using hmenu 0 (by simp)
  have hceil : (tupleLength rate b : ℝ) ≤ rate*b+1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hrate.le hb0)).le
  have hb' : (8 : ℝ)/δ ≤ b :=
    (Nat.le_ceil _).trans (by exact_mod_cast hb)
  have hlarge : (8 : ℝ) ≤ δ*b := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hb'
  have hlinear : 2*((b : ℝ)+r) ≤ (δ/4)*((b : ℝ)+r)^2 := by
    have hmul := mul_nonneg (show 0 ≤ δ*((b : ℝ)+r)-8 by nlinarith) (add_nonneg hb0 hr0)
    nlinarith
  have hquad : (b : ℝ)*((b : ℝ)+r) ≤ ((b : ℝ)+r)^2 := by
    nlinarith [mul_nonneg hr0 (add_nonneg hb0 hr0)]
  have herr : boundedWordError 14 b 0 +
      2*((b : ℝ)+r)*tupleLength rate b ≤ δ*((b : ℝ)+r)^2 := by
    have ht := mul_le_mul_of_nonneg_left hceil
      (show 0 ≤ 2*((b : ℝ)+r) by positivity)
    have hs : (b : ℝ)^2 ≤ ((b : ℝ)+r)^2 := by nlinarith
    dsimp [rate] at ht
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ δ/4 by positivity),
      mul_le_mul_of_nonneg_left hquad (show 0 ≤ δ/4 by positivity)]
  calc
    solubleMarkedC4Moment b r ≤
        (((menuSize b * 2^(2*b*tupleLength rate b) : ℕ) : ℝ) *
          (2 : ℝ)^(2*r*tupleLength rate b)) * OrbitCutoffFamilies.solubleCount C b r :=
      hfinite b r
    _ ≤ (2 : ℝ)^(boundedWordError 14 b 0 +
          2*((b : ℝ)+r)*tupleLength rate b) * OrbitCutoffFamilies.solubleCount C b r :=
      mul_le_mul_of_nonneg_right (code_cost_le rate b r)
        (Finset.sum_nonneg (fun _ _ => by positivity))
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) herr)
      (Finset.sum_nonneg (fun _ _ => by positivity))

end SymmetricSubgroupAsymptotics.MarkedC4.ConstructedLargeOrbitCutoff
end
