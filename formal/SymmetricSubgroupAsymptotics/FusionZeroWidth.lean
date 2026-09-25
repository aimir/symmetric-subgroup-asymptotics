import SymmetricSubgroupAsymptotics.FusionNumerics

/-!
# The zero-prefix-width fusion endpoint

When every positive moment has the same finite bound, each nonnegative
source weight is at most one. This excludes the strict hot event without
choosing a moment by a formula that divides by the prefix width.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Uniform control of all positive moments by one finite real number
forces every individual source weight to be at most one. -/
theorem fusionZeroWidth_weight_le_one {ι : Type*} [Fintype ι]
    (Φ : ι → ℝ) (hΦ : ∀ i, 0 ≤ Φ i) {M : ℝ}
    (hmoment : ∀ q : ℕ, 1 ≤ q → ∑ i, Φ i ^ q ≤ M) (i : ι) :
    Φ i ≤ 1 := by
  by_contra hi
  have hi : 1 < Φ i := lt_of_not_ge hi
  obtain ⟨q,hq⟩ := pow_unbounded_of_one_lt (max M 1) hi
  have hqpos : 1 ≤ q := by
    by_contra h
    have hzero : q = 0 := by omega
    subst q
    exact (not_lt_of_ge (le_max_right M 1)) (by simpa only [pow_zero] using hq)
  have hterm : Φ i ^ q ≤ ∑ j, Φ j ^ q :=
    Finset.single_le_sum (fun j _ => pow_nonneg (hΦ j) q) (Finset.mem_univ i)
  exact (not_lt_of_ge ((hterm.trans (hmoment q hqpos)).trans (le_max_left M 1))) hq

/-- There are no strict hot sources at any threshold at least one. -/
theorem fusionZeroWidth_hot_empty {ι : Type*} [Fintype ι]
    (Φ : ι → ℝ) (hΦ : ∀ i, 0 ≤ Φ i) {M t : ℝ}
    (hmoment : ∀ q : ℕ, 1 ≤ q → ∑ i, Φ i ^ q ≤ M) (ht : 1 ≤ t) :
    Finset.univ.filter (fun i => t < Φ i) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro i _
  exact not_lt_of_ge ((fusionZeroWidth_weight_le_one Φ hΦ hmoment i).trans ht)

/-- The local envelope becomes a direct bound when the moment has zero
prefix width. Its cocycle factor is still charged exactly once. -/
theorem fusionZeroWidth_direct_bound {ι : Type*} [Fintype ι]
    (f Φ : ι → ℝ) (hΦ : ∀ i, 0 ≤ Φ i) {M D : ℝ}
    (hmoment : ∀ q : ℕ, 1 ≤ q → ∑ i, Φ i ^ q ≤ M)
    (hD : 0 ≤ D) (hf : ∀ i, f i ≤ D * Φ i) (i : ι) :
    f i ≤ D := by
  exact (hf i).trans (by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (fusionZeroWidth_weight_le_one Φ hΦ hmoment i) hD)

end SymmetricSubgroupAsymptotics
