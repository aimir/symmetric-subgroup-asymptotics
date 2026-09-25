import SymmetricSubgroupAsymptotics.FusionShiftedMenu

/-! Actual finite-width cold entries form a nonnegative forward row with a
proved contractive aggregate in the ambient degree. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The original kernel is assigned to its actual untouched complement. -/
def fusionFiniteColdRow {ι : Type*} [Fintype ι] (h : ι → ℕ)
    (D a g : ι → ℝ) (n b : ℕ) : ℝ :=
  ∑ i, if b + 2 * h i = n then fusionColdKernel b (h i) (D i) (a i) (g i) else 0

theorem fusionFiniteColdRow_nonneg {ι : Type*} [Fintype ι] (h : ι → ℕ)
    (D a g : ι → ℝ) (hD : ∀ i, 0 ≤ D i) (ha : ∀ i, 0 < a i) (n b : ℕ) :
    0 ≤ fusionFiniteColdRow h D a g n b := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact fusionColdKernel_nonneg b (h i) (hD i) (ha i)
  · exact le_rfl

theorem fusionFiniteColdRow_forward {ι : Type*} [Fintype ι] (h : ι → ℕ)
    (D a g : ι → ℝ) (hh : ∀ i, 0 < h i) {n b : ℕ} (hnb : n ≤ b) :
    fusionFiniteColdRow h D a g n b = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : b + 2 * h i ≠ n := by have := hh i; omega
  simp only [if_neg hi]

/-- Exact assembly, including arbitrary weights on the complete complement. -/
theorem fusionFiniteColdRow_weighted_sum {ι : Type*} [Fintype ι]
    (h : ι → ℕ) (D a g : ι → ℝ) (hh : ∀ i, 0 < h i)
    (f : ℕ → ℝ) (n : ℕ) (hn : ∀ i, 2 * h i ≤ n) :
    ∑ b ∈ Finset.range n, fusionFiniteColdRow h D a g n b * f b =
      ∑ i, fusionColdKernel (n - 2 * h i) (h i) (D i) (a i) (g i) * f (n - 2 * h i) := by
  simp only [fusionFiniteColdRow, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hi : n - 2 * h i < n := by have := hh i; have := hn i; omega
  rw [Finset.sum_eq_single (n - 2 * h i)]
  · rw [if_pos (Nat.sub_add_cancel (hn i))]
  · intro b _ hb
    have hne : b + 2 * h i ≠ n := by omega
    simp [hne]
  · simp [Finset.mem_range.mpr hi]

/-- The row aggregate decays exponentially, with one common rate for all
original action weights and all parity classes. -/
theorem fusionFiniteColdRow_decay {ι : Type*} [Fintype ι]
    (h : ι → ℕ) (D a g : ι → ℝ) (hh : ∀ i, 0 < h i)
    (hD : ∀ i, 0 ≤ D i) (ha : ∀ i, 0 < a i) (hg : ∀ i, 0 < g i) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, fusionFiniteColdRow h D a g n b ≤
        C * (2 : ℝ)^(-κ * (n : ℝ)) := by
  obtain ⟨C, κ, hC, hκ, hb⟩ := fusionColdKernel_shifted_finite_sum h D a g hD ha hg
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hb, Filter.eventually_all.mpr (fun i => eventually_ge_atTop (2 * h i))]
    with n hn hw
  have he := fusionFiniteColdRow_weighted_sum h D a g hh (fun _ => 1) n hw
  simpa only [mul_one] using he.le.trans (by simpa only [mul_one] using hn)

/-- In particular the original cold row is eventually contractive, before
assuming any bound on the total subgroup sequence. -/
theorem fusionFiniteColdRow_contractive {ι : Type*} [Fintype ι]
    (h : ι → ℕ) (D a g : ι → ℝ) (hh : ∀ i, 0 < h i)
    (hD : ∀ i, 0 ≤ D i) (ha : ∀ i, 0 < a i) (hg : ∀ i, 0 < g i) :
    ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, fusionFiniteColdRow h D a g n b ≤ 1 / 2 := by
  obtain ⟨C, κ, hC, hκ, hb⟩ := fusionFiniteColdRow_decay h D a g hh hD ha hg
  filter_upwards [hb, eventually_exponential_le_inv_rpow hκ 1,
    eventually_ge_atTop (max 1 ⌈2 * C⌉₊)] with n hn he hlarge
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hlarge
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnC : 2 * C ≤ (n : ℝ) := (Nat.le_ceil (2 * C)).trans
    (by exact_mod_cast (le_max_right _ _).trans hlarge)
  rw [Real.rpow_one] at he
  apply hn.trans ((mul_le_mul_of_nonneg_left he hC.le).trans ?_)
  rw [mul_one_div]
  exact (div_le_iff₀ hnpos).mpr (by linarith)

end SymmetricSubgroupAsymptotics
