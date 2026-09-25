import SymmetricSubgroupAsymptotics.FusionArbitraryWidth

/-! Actual finite-width cold entries form a nonnegative forward row with a
proved contractive aggregate in the ambient degree. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A literal finite continuation menu, allowing polynomial local factors. -/
def fusionForwardRow {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (f : ι → ℕ → ℝ) (n b : ℕ) : ℝ :=
  ∑ i, if b+w i=n then f i b else 0

theorem fusionForwardRow_nonneg {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (f : ι → ℕ → ℝ) (hf : ∀ i b, 0≤f i b) (n b : ℕ) :
    0≤fusionForwardRow w f n b := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hf i b
  · exact le_rfl

theorem fusionForwardRow_forward {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (f : ι → ℕ → ℝ) (hw : ∀ i, 0<w i) {n b : ℕ} (hn : n≤b) :
    fusionForwardRow w f n b=0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : b+w i≠n := by have := hw i; omega
  simp only [if_neg hi]

/-- Every local entry retains the weight of its actual complete complement. -/
theorem fusionForwardRow_weighted_sum {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (f : ι → ℕ → ℝ) (hw : ∀ i, 0<w i)
    (s : ℕ → ℝ) (n : ℕ) (hn : ∀ i, w i≤n) :
    ∑ b ∈ Finset.range n, fusionForwardRow w f n b*s b =
      ∑ i, f i (n-w i)*s (n-w i) := by
  simp only [fusionForwardRow,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hi : n-w i<n := by have := hw i; have := hn i; omega
  rw [Finset.sum_eq_single (n-w i)]
  · rw [if_pos (Nat.sub_add_cancel (hn i))]
  · intro b _ hb
    have hne : b+w i≠n := by omega
    simp [hne]
  · simp [Finset.mem_range.mpr hi]

theorem fusionForwardRow_decay {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (f : ι → ℕ → ℝ) (hw : ∀ i, 0<w i)
    (hf : ∀ i, ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ b : ℕ in atTop,
      f i b≤C*(2:ℝ)^(-κ*(b:ℝ))) :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, fusionForwardRow w f n b≤C*(2:ℝ)^(-κ*(n:ℝ)) := by
  have h : ∀ i, ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ b : ℕ in atTop,
      f i b≤C*(2:ℝ)^(-κ*(b:ℝ)^1) := by simpa using hf
  obtain ⟨C,κ,hC,hκ,hb⟩ := fusion_finite_shifted_decay f w 1 h
  refine ⟨C,κ,hC,hκ,?_⟩
  filter_upwards [hb,Filter.eventually_all.mpr (fun i => eventually_ge_atTop (w i))]
    with n hn hwidth
  have he := fusionForwardRow_weighted_sum w f hw (fun _ => 1) n hwidth
  simpa only [mul_one,pow_one] using he.le.trans (by simpa only [mul_one,pow_one] using hn)

theorem fusionForwardRow_contractive {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (f : ι → ℕ → ℝ) (hw : ∀ i, 0<w i)
    (hf : ∀ i, ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ b : ℕ in atTop,
      f i b≤C*(2:ℝ)^(-κ*(b:ℝ))) :
    ∀ᶠ n : ℕ in atTop, ∑ b ∈ Finset.range n, fusionForwardRow w f n b≤1/2 := by
  obtain ⟨C,κ,hC,hκ,hb⟩ := fusionForwardRow_decay w f hw hf
  filter_upwards [hb,eventually_exponential_le_inv_rpow hκ 1,
    eventually_ge_atTop (max 1 ⌈2*C⌉₊)] with n hn he hlarge
  have hn1 : 1≤n := (le_max_left _ _).trans hlarge
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnC : 2*C≤(n:ℝ) := (Nat.le_ceil (2*C)).trans
    (by exact_mod_cast (le_max_right _ _).trans hlarge)
  rw [Real.rpow_one] at he
  apply hn.trans ((mul_le_mul_of_nonneg_left he hC.le).trans ?_)
  rw [mul_one_div]
  exact (div_le_iff₀ hnpos).mpr (by linarith)

/-- The original kernel is assigned to its actual untouched complement. -/
def fusionWidthColdRow {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (D a α : ι → ℝ) (n b : ℕ) : ℝ :=
  ∑ i, if b + w i = n then fusionWidthColdKernel b (w i) (D i) (a i) (α i) else 0

theorem fusionWidthColdRow_nonneg {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (D a α : ι → ℝ) (hD : ∀ i, 0 ≤ D i) (ha : ∀ i, 0 < a i) (n b : ℕ) :
    0 ≤ fusionWidthColdRow w D a α n b := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact fusionWidthColdKernel_nonneg b (w i) (hD i) (ha i)
  · exact le_rfl

theorem fusionWidthColdRow_forward {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (D a α : ι → ℝ) (hw : ∀ i, 0 < w i) {n b : ℕ} (hnb : n ≤ b) :
    fusionWidthColdRow w D a α n b = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : b + w i ≠ n := by have := hw i; omega
  simp only [if_neg hi]

/-- Exact assembly, including arbitrary weights on the complete complement. -/
theorem fusionWidthColdRow_weighted_sum {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (D a α : ι → ℝ) (hw : ∀ i, 0 < w i)
    (f : ℕ → ℝ) (n : ℕ) (hn : ∀ i, w i ≤ n) :
    ∑ b ∈ Finset.range n, fusionWidthColdRow w D a α n b * f b =
      ∑ i, fusionWidthColdKernel (n - w i) (w i) (D i) (a i) (α i) * f (n - w i) := by
  simp only [fusionWidthColdRow, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hi : n - w i < n := by have := hw i; have := hn i; omega
  rw [Finset.sum_eq_single (n - w i)]
  · rw [if_pos (Nat.sub_add_cancel (hn i))]
  · intro b _ hb
    have hne : b + w i ≠ n := by omega
    simp [hne]
  · simp [Finset.mem_range.mpr hi]

/-- The row aggregate decays exponentially, with one common rate for all
original action weights and all parity classes. -/
theorem fusionWidthColdRow_decay {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (D a α : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hD : ∀ i, 0 ≤ D i) (ha : ∀ i, 0 < a i) (hgap : ∀ i, α i < (halfDegree (w i):ℝ)/4) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, fusionWidthColdRow w D a α n b ≤
        C * (2 : ℝ)^(-κ * (n : ℝ)) := by
  obtain ⟨C, κ, hC, hκ, hb⟩ := fusionWidthColdKernel_shifted_sum w D a α hD ha hgap
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hb, Filter.eventually_all.mpr (fun i => eventually_ge_atTop (w i))]
    with n hn hwidth
  have he := fusionWidthColdRow_weighted_sum w D a α hw (fun _ => 1) n hwidth
  simpa only [mul_one] using he.le.trans (by simpa only [mul_one] using hn)

/-- In particular the original cold row is eventually contractive, before
assuming any bound on the total subgroup sequence. -/
theorem fusionWidthColdRow_contractive {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (D a α : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hD : ∀ i, 0 ≤ D i) (ha : ∀ i, 0 < a i) (hgap : ∀ i, α i < (halfDegree (w i):ℝ)/4) :
    ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, fusionWidthColdRow w D a α n b ≤ 1 / 2 := by
  obtain ⟨C, κ, hC, hκ, hb⟩ := fusionWidthColdRow_decay w D a α hw hD ha hgap
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
