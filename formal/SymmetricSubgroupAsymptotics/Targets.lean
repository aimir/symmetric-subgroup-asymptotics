import SymmetricSubgroupAsymptotics.Statements

/-!
# The common-threshold formulation of the targets

The equivalences here only reorganize quantifiers in the approved targets.
They do not prove any of T1, T2 or T3.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- The quantified joint statement in Section 5 of the specification. The
four positive real constants and the single threshold are uniform in degree,
parity and residue class. -/
def SharedThresholdTargets : Prop :=
  ∃ c K1 K2 K3 : ℝ, 0 < c ∧ 0 < K1 ∧ 0 < K2 ∧ 0 < K3 ∧
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      (|(subgroupCount n : ℝ) / exactBenchmark n - 1| ≤
        K1 * (2 : ℝ) ^ (-c * (n : ℝ))) ∧
      (|(subgroupCount n : ℝ) / saddleBenchmark n - 1| ≤ K2 / (n : ℝ)) ∧
      (|(subgroupCount n : ℝ) / elementaryBenchmark n - 1 - firstCorrection n| ≤
        K3 / Real.sqrt (n : ℝ))

/-- Taking the maximum of the three thresholds proves the shared-threshold
formulation, and restricting each conjunction gives the converse. -/
theorem targets_iff_shared_threshold :
    (T1 ∧ T2 ∧ T3) ↔ SharedThresholdTargets := by
  constructor
  · rintro ⟨⟨c, K1, hc, hK1, N1, hN1, h1⟩,
      ⟨K2, hK2, N2, _, h2⟩, ⟨K3, hK3, N3, _, h3⟩⟩
    refine ⟨c, K1, K2, K3, hc, hK1, hK2, hK3, max N1 (max N2 N3),
      hN1.trans (le_max_left _ _), ?_⟩
    intro n hn
    have hn1 : N1 ≤ n := (le_max_left _ _).trans hn
    have hn2 : N2 ≤ n := (le_max_left N2 N3).trans ((le_max_right _ _).trans hn)
    have hn3 : N3 ≤ n := (le_max_right N2 N3).trans ((le_max_right _ _).trans hn)
    exact ⟨h1 n hn1, h2 n hn2, h3 n hn3⟩
  · rintro ⟨c, K1, K2, K3, hc, hK1, hK2, hK3, N, hN, h⟩
    exact ⟨⟨c, K1, hc, hK1, N, hN, fun n hn => (h n hn).1⟩,
      ⟨K2, hK2, N, hN, fun n hn => (h n hn).2.1⟩,
      ⟨K3, hK3, N, hN, fun n hn => (h n hn).2.2⟩⟩

/-- The meaning and positivity obligations remain present when the targets
are written with one threshold. -/
theorem allTargets_iff_definitionChecks_and_shared_threshold :
    AllTargets ↔ DefinitionChecks ∧ SharedThresholdTargets := by
  exact and_congr_right fun _ => targets_iff_shared_threshold

end SymmetricSubgroupAsymptotics
