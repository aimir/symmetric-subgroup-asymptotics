import SymmetricSubgroupAsymptotics.BinarySmallOrbitPowerDirect
import SymmetricSubgroupAsymptotics.FusionActualOrbitCharts

/-! Intrinsic fixed-power small-order orbit counting. Membership is stated
using an actual orbit of the original subgroup and the faithful image on
that orbit. The chart used for fusion is constructed internally; the
subgroup, its complement, and all correlations are unchanged.

The family is unmarked, so neither the selected point nor an orbit chart
contributes a multiplicity. The direct row and its fixed-width contraction
are exactly those of BinarySmallOrbitPowerDirect.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinarySmallOrbitPowerIntrinsic

open BinarySmallOrbitPowerDirect

/-- An original subgroup has an actual binary orbit of the prescribed
power degree and bounded actual orbit-image order. The whole subgroup and
its complementary orbits need not be binary. -/
def physicalFamily (k n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ x : Fin n,
    Nat.card (MulAction.orbit H x) = BinarySmallOrbitPowerDirect.degree k ∧
    IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x) ∧
    Nat.card (FusionActualOrbitCharts.orbitImage H x) ≤ 2^(BinarySmallOrbitPowerDirect.halfDegree k)}

/-- Construct a chart from this particular actual orbit, transporting its
full image rather than assuming a chart-action classification. -/
def orbitChart (k : ℕ) {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit H x) = BinarySmallOrbitPowerDirect.degree k)
    (hP : IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x))
    (hcard : Nat.card (FusionActualOrbitCharts.orbitImage H x) ≤ 2^(BinarySmallOrbitPowerDirect.halfDegree k)) :
    BinarySmallOrbitPowerDirect.OrbitChart k H where
  chart := FusionActualOrbitCharts.chart H x hw
  preserves := FusionActualOrbitCharts.chart_preserves H x hw
  binary := FusionActualOrbitCharts.chartAction_isPGroup H x hw 2 hP
  transitive := FusionActualOrbitCharts.chartAction_transitive H x hw
  order_le := by
    change Nat.card (FusionActualOrbitCharts.chartAction H x hw) ≤ _
    rw [FusionActualOrbitCharts.chartAction_card]
    exact hcard

/-- The constructed chart labels exactly the chosen original orbit. -/
theorem orbitChart_first_range (k : ℕ) {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit H x) = BinarySmallOrbitPowerDirect.degree k)
    (hP : IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x))
    (hcard : Nat.card (FusionActualOrbitCharts.orbitImage H x) ≤ 2^(BinarySmallOrbitPowerDirect.halfDegree k)) :
    Set.range (fun i : Fin (BinarySmallOrbitPowerDirect.degree k) =>
      (orbitChart k H x hw hP hcard).chart (Sum.inl i)) = MulAction.orbit H x :=
  FusionActualOrbitCharts.chart_first_range H x hw

/-- Intrinsic membership produces, rather than assumes, a valid physical
chart. The actual subgroup is the same element of the containing family. -/
theorem family_subset (k n : ℕ) :
    physicalFamily k n ⊆ BinarySmallOrbitPowerDirect.physicalFamily k n := by
  intro H hH
  obtain ⟨x, hw, hP, hcard⟩ := hH
  exact ⟨orbitChart k H x hw hP hcard⟩

/-- A member's actual orbit fits inside its original point set. -/
theorem degree_le_of_mem {k n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ physicalFamily k n) : BinarySmallOrbitPowerDirect.degree k ≤ n := by
  obtain ⟨x, hw, _, _⟩ := hH
  exact FusionActualOrbitCharts.degree_le H x hw

theorem card_le_chartFamily (k n : ℕ) :
    Nat.card (physicalFamily k n) ≤
      Nat.card (BinarySmallOrbitPowerDirect.physicalFamily k n) :=
  Nat.card_le_card_of_injective (Set.inclusion (family_subset k n))
    (Set.inclusion_injective _)

/-- The exact checked row bounds the intrinsic unmarked family. No
chart, cover, point-choice multiplicity, or ordinary count bound is input. -/
theorem direct_recurrence (k : ℕ) (hk : 4 ≤ k)
    (hMaroti : NilpotentConjugacyClassInput) (n : ℕ) (hn : BinarySmallOrbitPowerDirect.degree k ≤ n) :
    (Nat.card (physicalFamily k n) : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n, BinarySmallOrbitPowerDirect.directRow k hk n m *
        ((subgroupCount m : ℝ) / exactBenchmark m) := by
  have hc : (Nat.card (physicalFamily k n) : ℝ) ≤
      Nat.card (BinarySmallOrbitPowerDirect.physicalFamily k n) := by
    exact_mod_cast card_le_chartFamily k n
  exact (div_le_div_of_nonneg_right hc (exactBenchmark_pos n).le).trans
    (BinarySmallOrbitPowerDirect.direct_recurrence k hk hMaroti n hn)

/-- Earlier-owner or other arbitrary exclusions restrict this same
intrinsic unmarked family, without changing its direct row. -/
theorem filtered_direct_recurrence (k : ℕ) (hk : 4 ≤ k)
    (hMaroti : NilpotentConjugacyClassInput) (n : ℕ) (hn : BinarySmallOrbitPowerDirect.degree k ≤ n)
    (R : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : physicalFamily k n // R H.1} : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n, BinarySmallOrbitPowerDirect.directRow k hk n m *
        ((subgroupCount m : ℝ) / exactBenchmark m) := by
  have hc : Nat.card {H : physicalFamily k n // R H.1} ≤
      Nat.card (physicalFamily k n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (direct_recurrence k hk hMaroti n hn)

end SymmetricSubgroupAsymptotics.BinarySmallOrbitPowerIntrinsic

end

