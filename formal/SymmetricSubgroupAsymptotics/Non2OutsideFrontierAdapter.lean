import SymmetricSubgroupAsymptotics.Non2OutsideOrbitMenu
import SymmetricSubgroupAsymptotics.OrdinaryFrontierClosure

/-!
# Ambient-degree adapter and disjoint width split for the outside frontier

The outside frontier used by the final recurrence is indexed by ambient
degree through rank and parity.  This file identifies it with the literal
subgroup set covered by the non-2 menu and partitions its source using the
single selected bad orbit, so a subgroup with several bad orbits is never
charged to both the small and growing sectors.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace RepeatedMarkerOwnerBound

open OrdinaryFrontierClosure

/-- The ambient-degree frontier is exactly the normalized cardinality of
the literal outside subgroup set. -/
theorem outsideFrontierRatio_eq_subgroupSet (n : ℕ) :
    outsideFrontierRatio n =
      (Nat.card (OutsideFitsSubgroupSet (halfDegree n) (parity n)) : ℝ) /
        exactBenchmark n := by
  unfold outsideFrontierRatio outsideFitsRatio
  rw [← outsideFitsSubgroupSet_card]
  exact congrArg
    (fun x : ℝ =>
      (Nat.card (OutsideFitsSubgroupSet (halfDegree n) (parity n)) : ℝ) / x)
    (congrArg exactBenchmark (MarkerDegreeForwardRow.degree_identity n))

abbrev SmallSelectedOutsideFamily (N epsilon : ℕ) :=
  {H : OutsideFitsFamily N epsilon // selectedOutsideWidth N epsilon H ≤ 4}

abbrev GrowingSelectedOutsideFamily (N epsilon : ℕ) :=
  {H : OutsideFitsFamily N epsilon //
    ¬ selectedOutsideWidth N epsilon H ≤ 4}

def outsideFitsSelectedWidthPartitionEquiv (N epsilon : ℕ) :
    OutsideFitsFamily N epsilon ≃
      SmallSelectedOutsideFamily N epsilon ⊕
        GrowingSelectedOutsideFamily N epsilon :=
  (Equiv.sumCompl (fun H : OutsideFitsFamily N epsilon =>
    selectedOutsideWidth N epsilon H ≤ 4)).symm

theorem outsideFits_selectedWidth_card_partition (N epsilon : ℕ) :
    Nat.card (OutsideFitsFamily N epsilon) =
      Nat.card (SmallSelectedOutsideFamily N epsilon) +
        Nat.card (GrowingSelectedOutsideFamily N epsilon) := by
  rw [Nat.card_congr (outsideFitsSelectedWidthPartitionEquiv N epsilon),
    Nat.card_sum]

theorem smallSelectedOutside_width (N epsilon : ℕ)
    (H : SmallSelectedOutsideFamily N epsilon) :
    selectedOutsideWidth N epsilon H.1 = 3 ∨
      selectedOutsideWidth N epsilon H.1 = 4 := by
  have hgt := selectedOutsideWidth_gt_two N epsilon H.1
  omega

theorem growingSelectedOutside_width (N epsilon : ℕ)
    (H : GrowingSelectedOutsideFamily N epsilon) :
    5 ≤ selectedOutsideWidth N epsilon H.1 := by
  omega

end RepeatedMarkerOwnerBound
end SymmetricSubgroupAsymptotics

end
