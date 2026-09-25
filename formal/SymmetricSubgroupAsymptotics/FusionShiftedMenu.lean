import SymmetricSubgroupAsymptotics.FusionCold
import SymmetricSubgroupAsymptotics.FusionHot
import Mathlib.Data.Finset.Max

/-! Finite original-weight menus are evaluated at their different complete
complement degrees `n - 2*h`, with one ambient exponential decay rate. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

private theorem fusion_finite_positive_lower {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ i, κ ≤ r i := by
  let f : Option ι → ℝ := fun o => o.elim 1 r
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨f j, ?_, fun i => hj (some i) (Finset.mem_univ _)⟩
  cases j with
  | none => norm_num [f]
  | some i => exact hr i

/-- A finite family of fixed shifts preserves any positive power-exponential
rate. The complement degree for each entry is kept separately. -/
theorem fusion_finite_shifted_decay {ι : Type*} [Fintype ι]
    (f : ι → ℕ → ℝ) (w : ι → ℕ) (p : ℕ)
    (h : ∀ i, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ b : ℕ in atTop,
      f i b ≤ C * (2 : ℝ)^(-κ * (b : ℝ)^p)) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i, f i (n - w i) ≤ C * (2 : ℝ)^(-κ * (n : ℝ)^p) := by
  choose C r hC hr hb using h
  obtain ⟨κ, hκ, hκr⟩ := fusion_finite_positive_lower
    (fun i => r i / (2 : ℝ)^p) (fun i => div_pos (hr i) (by positivity))
  have hshift : ∀ i, ∀ᶠ n : ℕ in atTop,
      f i (n - w i) ≤ C i * (2 : ℝ)^(-r i * ((n - w i : ℕ) : ℝ)^p) :=
    fun i => (tendsto_sub_atTop_nat (w i)).eventually (hb i)
  have hlarge : ∀ᶠ n : ℕ in atTop, ∀ i, 2 * w i ≤ n :=
    Filter.eventually_all.mpr (fun i => eventually_ge_atTop (2 * w i))
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  refine ⟨(∑ i, C i) + 1, κ, by positivity, hκ, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hshift, hlarge] with n hn hbig
  calc
    _ ≤ ∑ i, C i * (2 : ℝ)^(-κ * (n : ℝ)^p) := by
      apply Finset.sum_le_sum
      intro i _
      apply (hn i).trans
      apply mul_le_mul_of_nonneg_left _ (hC i).le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hw : w i ≤ n := by have := hbig i; omega
      have hnle : (n : ℝ) ≤ 2 * ((n - w i : ℕ) : ℝ) := by
        rw [Nat.cast_sub hw]
        have := hbig i
        have : 2 * (w i : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
        linarith
      have hp := pow_le_pow_left₀ (show 0 ≤ (n : ℝ) by positivity) hnle p
      rw [mul_pow] at hp
      have hk : κ * (2 : ℝ)^p ≤ r i :=
        (le_div_iff₀ (by positivity)).mp (hκr i)
      have h1 := mul_le_mul_of_nonneg_left hp hκ.le
      have h2 := mul_le_mul_of_nonneg_right hk
        (pow_nonneg (show 0 ≤ ((n - w i : ℕ) : ℝ) by positivity) p)
      nlinarith
    _ = (∑ i, C i) * (2 : ℝ)^(-κ * (n : ℝ)^p) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- A cold continuation row in the actual ambient degree. Its entries need
not remove the same number of points or have the same action divisor. -/
theorem fusionColdKernel_shifted_finite_sum {ι : Type*} [Fintype ι]
    (h : ι → ℕ) (D a g : ι → ℝ)
    (hD : ∀ i, 0 ≤ D i) (ha : ∀ i, 0 < a i) (hg : ∀ i, 0 < g i) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i, fusionColdKernel (n - 2 * h i) (h i) (D i) (a i) (g i) ≤
        C * (2 : ℝ)^(-κ * (n : ℝ)) := by
  have he := fusion_finite_shifted_decay
    (fun i b => fusionColdKernel b (h i) (D i) (a i) (g i))
    (fun i => 2 * h i) 1 (fun i => ?_)
  · simpa using he
  · obtain ⟨C, hC, hb⟩ := fusionColdKernel_eventually (h i) (hD i) (ha i) (hg i)
    exact ⟨C, g i / 32, hC, div_pos (hg i) (by norm_num), by simpa using hb⟩

/-- Zero graph width has an empty strict hot set and hence a zero hot entry. -/
def fusionMenuHotKernel (s : ℕ → ℝ) (b h v : ℕ) (D a e : ℝ) : ℝ :=
  if v = 0 then 0 else fusionHotKernel s b h v D a e

/-- The complete finite hot sum is quadratically small in the ambient degree,
including zero-width entries and both parities. Only the coarse count input
is assumed; no bound on the normalized total count is used. -/
theorem fusionMenuHotKernel_shifted_finite_sum {ι : Type*} [Fintype ι]
    (s : ℕ → ℝ) (hs : FusionCoarseEstimate s) (h v : ι → ℕ) (D a e : ι → ℝ)
    (hD : ∀ i, 0 ≤ D i) (ha : ∀ i, 0 < a i) (he : ∀ i, 0 < e i) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i, fusionMenuHotKernel s (n - 2 * h i) (h i) (v i) (D i) (a i) (e i) ≤
        C * (2 : ℝ)^(-κ * (n : ℝ)^2) := by
  apply fusion_finite_shifted_decay
    (fun i b => fusionMenuHotKernel s b (h i) (v i) (D i) (a i) (e i))
    (fun i => 2 * h i) 2
  intro i
  by_cases hv : v i = 0
  · refine ⟨1, 1, by norm_num, by norm_num, Filter.Eventually.of_forall (fun b => ?_)⟩
    simp only [fusionMenuHotKernel, hv]
    positivity
  · simpa only [fusionMenuHotKernel, if_neg hv] using
      fusionHotKernel_eventually s hs (h i) (v i) (Nat.pos_of_ne_zero hv)
        (hD i) (ha i) (he i)

end SymmetricSubgroupAsymptotics
