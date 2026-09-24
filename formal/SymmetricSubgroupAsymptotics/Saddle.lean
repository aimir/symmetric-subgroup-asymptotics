import SymmetricSubgroupAsymptotics.Foundations

/-!
# The positive saddle

The infimum in `saddleRadius` is the unique positive solution of the saddle
equation at every positive rank. These results justify the saddle benchmark's
denominator without adding any assumptions to its definition.
-/

set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics

@[simp] theorem saddleMean_zero : saddleMean 0 = 0 := by
  norm_num [saddleMean]

theorem continuous_saddleMean : Continuous saddleMean := by
  unfold saddleMean
  fun_prop

theorem saddleMean_strictMonoOn : StrictMonoOn saddleMean (Set.Ici 0) := by
  intro x hx y hy hxy
  have h₂ : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy.le 2
  have h₄ : x ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hx hxy.le 4
  dsimp [saddleMean]
  linarith

theorem saddleMean_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ saddleMean x := by
  unfold saddleMean
  positivity

theorem saddleMean_pos {x : ℝ} (hx : 0 < x) : 0 < saddleMean x := by
  unfold saddleMean
  positivity

theorem exists_positive_saddle (r : ℕ) (hr : 0 < r) :
    ∃ x : ℝ, 0 < x ∧ saddleMean x = (r : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hbound : (r : ℝ) ≤ saddleMean (2 * r) := by
    unfold saddleMean
    nlinarith [sq_nonneg (2 * (r : ℝ)), sq_nonneg ((2 * (r : ℝ)) ^ 2)]
  obtain ⟨x, hx, heq⟩ := intermediate_value_Icc
    (show (0 : ℝ) ≤ 2 * r by positivity)
    continuous_saddleMean.continuousOn
    (show (r : ℝ) ∈ Set.Icc (saddleMean 0) (saddleMean (2 * r)) by
      exact ⟨by simp [hr'.le], hbound⟩)
  refine ⟨x, lt_of_le_of_ne hx.1 ?_, heq⟩
  intro hz
  subst x
  simp only [saddleMean_zero] at heq
  linarith

/-- Any positive solution is exactly the infimum used by the definition. -/
theorem saddleRadius_eq_of_pos_root (r : ℕ) {x : ℝ} (hx : 0 < x)
    (heq : saddleMean x = (r : ℝ)) : saddleRadius r = x := by
  unfold saddleRadius
  apply IsLeast.csInf_eq
  refine ⟨⟨hx.le, heq.ge⟩, ?_⟩
  intro y hy
  by_contra hxy
  have hlt := saddleMean_strictMonoOn hy.1 hx.le (lt_of_not_ge hxy)
  linarith [hy.2]

theorem saddleRadius_pos (r : ℕ) (hr : 0 < r) : 0 < saddleRadius r := by
  obtain ⟨x, hx, heq⟩ := exists_positive_saddle r hr
  rw [saddleRadius_eq_of_pos_root r hx heq]
  exact hx

theorem saddleMean_saddleRadius (r : ℕ) (hr : 0 < r) :
    saddleMean (saddleRadius r) = (r : ℝ) := by
  obtain ⟨x, hx, heq⟩ := exists_positive_saddle r hr
  rw [saddleRadius_eq_of_pos_root r hx heq]
  exact heq

theorem saddleRadius_unique (r : ℕ) {x : ℝ} (hx : 0 < x)
    (heq : saddleMean x = (r : ℝ)) : x = saddleRadius r :=
  (saddleRadius_eq_of_pos_root r hx heq).symm

@[simp] theorem saddleRadius_zero : saddleRadius 0 = 0 := by
  unfold saddleRadius
  apply IsLeast.csInf_eq
  exact ⟨by simp, fun _ hx => hx.1⟩

/-- The complete root obligation appearing in `DefinitionChecks`. -/
theorem saddle_positive_unique (r : ℕ) (hr : 0 < r) :
    0 < saddleRadius r ∧ saddleMean (saddleRadius r) = (r : ℝ) ∧
      ∀ x : ℝ, 0 < x → saddleMean x = (r : ℝ) → x = saddleRadius r := by
  exact ⟨saddleRadius_pos r hr, saddleMean_saddleRadius r hr,
    fun _ hx heq => saddleRadius_unique r hx heq⟩

theorem saddleVariance_pos {x : ℝ} (hx : 0 < x) : 0 < saddleVariance x := by
  unfold saddleVariance
  positivity

theorem saddleVariance_saddleRadius_pos (r : ℕ) (hr : 0 < r) :
    0 < saddleVariance (saddleRadius r) :=
  saddleVariance_pos (saddleRadius_pos r hr)

/-- Increasing the rank strictly increases the positive saddle. -/
theorem saddleRadius_lt_saddleRadius {r s : ℕ} (hr : 0 < r) (hrs : r < s) :
    saddleRadius r < saddleRadius s := by
  have hs : 0 < s := lt_trans hr hrs
  by_contra h
  have hmean := saddleMean_strictMonoOn.monotoneOn
    (saddleRadius_pos s hs).le (saddleRadius_pos r hr).le (le_of_not_gt h)
  rw [saddleMean_saddleRadius s hs, saddleMean_saddleRadius r hr] at hmean
  exact (not_le_of_gt hrs) (by exact_mod_cast hmean)

/-- At the root, the variance lies between the mean and four times the mean. -/
theorem saddleVariance_bounds (r : ℕ) (hr : 0 < r) :
    (r : ℝ) ≤ saddleVariance (saddleRadius r) ∧
      saddleVariance (saddleRadius r) ≤ 4 * r := by
  have hpos := (saddleRadius_pos r hr).le
  have heq := saddleMean_saddleRadius r hr
  unfold saddleMean at heq
  unfold saddleVariance
  constructor <;> nlinarith [sq_nonneg (saddleRadius r),
    sq_nonneg ((saddleRadius r) ^ 2)]

theorem saddleBenchmark_pos_of_gaussianSum_pos (n : ℕ)
    (hcount : 0 < binaryGaussianSum (halfDegree n)) : 0 < saddleBenchmark n := by
  unfold saddleBenchmark
  split_ifs with hn
  · norm_num
  · have hr : 0 < halfDegree n := Nat.div_pos (by omega) (by decide)
    have hρ := saddleRadius_pos (halfDegree n) hr
    have hv := saddleVariance_saddleRadius_pos (halfDegree n) hr
    have hcount' : (0 : ℝ) < binaryGaussianSum (halfDegree n) := by
      exact_mod_cast hcount
    have hfac : (0 : ℝ) < Nat.factorial n := by
      exact_mod_cast Nat.factorial_pos n
    dsimp
    positivity

theorem saddleBenchmark_pos (n : ℕ) : 0 < saddleBenchmark n :=
  saddleBenchmark_pos_of_gaussianSum_pos n (binaryGaussianSum_pos (halfDegree n))

end SymmetricSubgroupAsymptotics
