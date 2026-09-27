import SymmetricSubgroupAsymptotics.RepeatedMarkerPositiveFamily
import SymmetricSubgroupAsymptotics.MarkerDegreeForwardRow

/-!
# The actual positive-defect marker family in the ordinary recurrence

The source is the complete physical family over every support triple and
every compatible original exterior multiplicity. Its finite action menu is
explicit; coverage of a larger owner sector is not assumed implicitly.
The recurrence uses the complete ordinary subgroup count at actual smaller
degrees, with no bounded-target hypothesis. Such a hypothesis is used only
in the separate corollaries below.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerPositiveRecurrence

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegreeOne : ∀ a, Fintype.card (Ω a) ≠ 1)
    (hdegreeTwo : ∀ a, Fintype.card (Ω a) ≠ 2)

include hU htrans hsep hdegreeOne hdegreeTwo

/-- The actual physical count satisfies the complete forward row. The
only target sequence is the literal ordinary subgroup ratio. -/
theorem card_div_benchmark_le (N epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    (Nat.card (RepeatedMarkerPositiveFamily.Family Ω U N epsilon P) : ℝ) /
        exactBenchmark (2*N+epsilon) ≤
      ∑ m ∈ Finset.range (2*N+epsilon),
        MarkerForwardRow.kernel N epsilon m * ordinarySubgroupRatio m := by
  rw [MarkerForwardRow.weighted_sum_eq]
  exact RepeatedMarkerPositiveFamily.card_div_benchmark_le Ω U N epsilon hepsilon
    hU htrans hsep hdegreeOne hdegreeTwo P

/-- The same original physical count uses the degree-indexed row of the
ordinary recurrence, at both parities. -/
theorem card_div_benchmark_le_degree_row (N epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    (Nat.card (RepeatedMarkerPositiveFamily.Family Ω U N epsilon P) : ℝ) /
        exactBenchmark (2*N+epsilon) ≤
      ∑ m ∈ Finset.range (2*N+epsilon),
        MarkerDegreeForwardRow.kernel (2*N+epsilon) m * ordinarySubgroupRatio m := by
  have hhalf : halfDegree (2*N+epsilon) = N := by unfold halfDegree; omega
  have hparity : parity (2*N+epsilon) = epsilon := by unfold parity; omega
  simpa only [MarkerDegreeForwardRow.kernel,hhalf,hparity] using
    card_div_benchmark_le Ω U hU htrans hsep hdegreeOne hdegreeTwo N epsilon hepsilon P

/-- Bounded targets are an optional later corollary, not an input to the
actual forward-count theorem. Only strictly smaller degrees are used. -/
theorem card_div_benchmark_le_of_targets (N epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop)
    (A : ℝ) (hA : ∀ m < 2*N+epsilon, ordinarySubgroupRatio m ≤ A) :
    (Nat.card (RepeatedMarkerPositiveFamily.Family Ω U N epsilon P) : ℝ) /
        exactBenchmark (2*N+epsilon) ≤
      A * MarkerNormalizedRow.positiveDefectRow N epsilon := by
  apply (card_div_benchmark_le Ω U hU htrans hsep hdegreeOne hdegreeTwo
    N epsilon hepsilon P).trans
  calc
    _ ≤ ∑ m ∈ Finset.range (2*N+epsilon), MarkerForwardRow.kernel N epsilon m * A := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left (hA m (Finset.mem_range.mp hm))
        (MarkerForwardRow.kernel_nonneg N epsilon m)
    _ = _ := by
      rw [← Finset.sum_mul,MarkerForwardRow.row_sum_eq,mul_comm]

/-- The already proved numerical row contracts the complete physical
positive-defect family once a later uniform bound on smaller targets is
available. The threshold is independent of the original predicate and A. -/
theorem eventually_card_div_benchmark_le_of_targets :
    ∀ᶠ N : ℕ in atTop, ∀ epsilon : ℕ, epsilon ≤ 1 →
      ∀ P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop,
      ∀ A : ℝ, 0 ≤ A →
      (∀ m < 2*N+epsilon, ordinarySubgroupRatio m ≤ A) →
      (Nat.card (RepeatedMarkerPositiveFamily.Family Ω U N epsilon P) : ℝ) /
          exactBenchmark (2*N+epsilon) ≤ A * (2 : ℝ)^(-(N : ℝ)/10) := by
  filter_upwards [MarkerForwardRow.eventually_both_parities] with N hN
  intro epsilon hepsilon P A hA htargets
  apply (card_div_benchmark_le_of_targets Ω U hU htrans hsep hdegreeOne hdegreeTwo
    N epsilon hepsilon P A htargets).trans
  apply mul_le_mul_of_nonneg_left _ hA
  simpa only [MarkerForwardRow.row_sum_eq] using hN epsilon hepsilon

end SymmetricSubgroupAsymptotics.RepeatedMarkerPositiveRecurrence

end
