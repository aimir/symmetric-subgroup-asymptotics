import SymmetricSubgroupAsymptotics.BinarySmallOrbit16Physical
import SymmetricSubgroupAsymptotics.BinaryOrderSevenCharacterDirectFusion
import SymmetricSubgroupAsymptotics.BinaryTransitivePowerSevenBoundary
import SymmetricSubgroupAsymptotics.FusionActualOrbitCharts

/-!
# Unconditional direct counting for small-order sixteen-point orbits

The actual binary permutation class theorem supplies the seven-power
character rate internally. All original actions of degree sixteen and
order at most 256, and every original normal axis, enter the same physical
row. The family is unmarked and its complete exterior is unrestricted.

Both the chart family and the intrinsic actual-orbit family have a direct
forward recurrence, with exponential row decay and arbitrary exclusions.
No class-count, coarse-count, coverage, or final-count premise remains.
The earlier interfaces with the distinct 38/25 input are unchanged.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter

namespace SymmetricSubgroupAsymptotics.BinarySmallOrbit16SevenDirect

open BinaryTransitiveBoundary16Fusion

/-- The whole-normal choice on each literal accepted sixteen-point action
uses its actual order and its new seven-power character criterion. -/
def selection (i : BoundaryAction) : BinaryOrderSevenCharacterSelection (boundaryAction i) := by
  letI := boundaryAction_transitive i
  exact BinaryTransitivePowerSevenBoundary.selectionOfDegree 4 (by decide)
    (boundaryAction i) (by decide) (by simpa using boundaryAction_card_le i)

theorem selection_prefixDegree_le (i : BoundaryAction)
    (N : {N : Subgroup (boundaryAction i) // N.Normal}) :
    (selection i).prefixDegree N ≤ 14 := by
  letI := boundaryAction_transitive i
  exact BinaryTransitivePowerSevenBoundary.selectionOfDegree_prefixDegree_le
    4 (by decide) (boundaryAction i) (by decide)
    (by simpa using boundaryAction_card_le i) N

/-- The existing actual chart family is retained literally. -/
abbrev physicalFamily (n : ℕ) := BinarySmallOrbit16Physical.physicalFamily n

/-- Original action and normalizer multiplicities remain inside this row;
an existential choice of orbit or chart does not mark the counted subgroup. -/
def directRow (n m : ℕ) : ℝ :=
  binaryOrderSevenCharacterDirectRow (fun _ : BoundaryAction => 8)
    boundaryAction selection n m

/-- The actual unmarked family satisfies the complete ordinary forward
recurrence with the proved binary class rate, without an external input. -/
theorem direct_recurrence (n : ℕ) (hn : 16 ≤ n) :
    (Nat.card (physicalFamily n) : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ) / exactBenchmark m) :=
  binaryOrderSevenCharacterSelection_direct_recurrence
    (fun _ : BoundaryAction => 8) boundaryAction selection
    boundaryAction_isPGroup (fun _ => by change 0 < 8; decide)
    n (fun _ => hn) (physicalFamily n) (fun _ _ => True)
    (fun _ _ _ _ => trivial) (BinarySmallOrbit16Physical.cover hn)

theorem directRow_nonneg (n m : ℕ) : 0 ≤ directRow n m :=
  binaryOrderSevenCharacterDirectRow_nonneg
    (fun _ : BoundaryAction => 8) boundaryAction selection n m

theorem directRow_forward {n m : ℕ} (hnm : n ≤ m) : directRow n m = 0 :=
  binaryOrderSevenCharacterDirectRow_forward
    (fun _ : BoundaryAction => 8) boundaryAction selection
    (fun _ => by change 0 < 8; decide) hnm

/-- Exponential decay is proved for this same original weighted row
before any bound on the ordinary subgroup sequence. -/
theorem directRow_decay :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, directRow n m ≤ A * (2 : ℝ)^(-κ * (n : ℝ)) :=
  binaryOrderSevenCharacterDirectRow_decay
    (fun _ : BoundaryAction => 8) boundaryAction selection
    (fun _ => by change 0 < 8; decide)

theorem directRow_contractive :
    ∀ᶠ n : ℕ in atTop, ∑ m ∈ Finset.range n, directRow n m ≤ 1/2 :=
  binaryOrderSevenCharacterDirectRow_contractive
    (fun _ : BoundaryAction => 8) boundaryAction selection
    (fun _ => by change 0 < 8; decide)

/-- Earlier-owner or other exclusions only restrict the actual unmarked
family; no naturality of the extra predicate is required for this inclusion. -/
theorem filtered_direct_recurrence (n : ℕ) (hn : 16 ≤ n)
    (P : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : physicalFamily n // P H.1} : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ) / exactBenchmark m) := by
  have hc : Nat.card {H : physicalFamily n // P H.1} ≤ Nat.card (physicalFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (direct_recurrence n hn)

/-- An actual sixteen-point binary orbit with its actual image order.
The complete original group and its other orbits need not be binary. -/
def intrinsicFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ x : Fin n, Nat.card (MulAction.orbit H x) = 16 ∧
    IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x) ∧
    Nat.card (FusionActualOrbitCharts.orbitImage H x) ≤ 256}

/-- The chart is constructed from the actual orbit, and its restriction
image has exactly the original orbit-image cardinality. -/
def intrinsicOrbitChart {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit H x) = 16)
    (hP : IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x))
    (hcard : Nat.card (FusionActualOrbitCharts.orbitImage H x) ≤ 256) :
    BinarySmallOrbit16Physical.OrbitChart H where
  chart := FusionActualOrbitCharts.chart H x hw
  preserves := FusionActualOrbitCharts.chart_preserves H x hw
  binary := FusionActualOrbitCharts.chartAction_isPGroup H x hw 2 hP
  transitive := FusionActualOrbitCharts.chartAction_transitive H x hw
  order_le := by
    change Nat.card (FusionActualOrbitCharts.chartAction H x hw) ≤ _
    rw [FusionActualOrbitCharts.chartAction_card]
    exact hcard

theorem intrinsicOrbitChart_first_range {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit H x) = 16)
    (hP : IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x))
    (hcard : Nat.card (FusionActualOrbitCharts.orbitImage H x) ≤ 256) :
    Set.range (fun i : Fin 16 =>
      (intrinsicOrbitChart H x hw hP hcard).chart (Sum.inl i)) = MulAction.orbit H x :=
  FusionActualOrbitCharts.chart_first_range H x hw

theorem intrinsicFamily_subset (n : ℕ) : intrinsicFamily n ⊆ physicalFamily n := by
  intro H hH
  obtain ⟨x, hw, hP, hcard⟩ := hH
  exact ⟨intrinsicOrbitChart H x hw hP hcard⟩

theorem degree_le_of_intrinsic_mem {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ intrinsicFamily n) : 16 ≤ n := by
  obtain ⟨x, hw, _, _⟩ := hH
  exact FusionActualOrbitCharts.degree_le H x hw

theorem intrinsic_card_le_chartFamily (n : ℕ) :
    Nat.card (intrinsicFamily n) ≤ Nat.card (physicalFamily n) :=
  Nat.card_le_card_of_injective (Set.inclusion (intrinsicFamily_subset n))
    (Set.inclusion_injective _)

/-- The same direct row bounds the intrinsic orbit family. No point or
chart choice, action catalogue, or original-normal coverage is supplied. -/
theorem intrinsic_direct_recurrence (n : ℕ) (hn : 16 ≤ n) :
    (Nat.card (intrinsicFamily n) : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ) / exactBenchmark m) := by
  have hc : (Nat.card (intrinsicFamily n) : ℝ) ≤ Nat.card (physicalFamily n) := by
    exact_mod_cast intrinsic_card_le_chartFamily n
  exact (div_le_div_of_nonneg_right hc (exactBenchmark_pos n).le).trans
    (direct_recurrence n hn)

theorem intrinsic_filtered_direct_recurrence (n : ℕ) (hn : 16 ≤ n)
    (P : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : intrinsicFamily n // P H.1} : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ) / exactBenchmark m) := by
  have hc : Nat.card {H : intrinsicFamily n // P H.1} ≤ Nat.card (intrinsicFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (intrinsic_direct_recurrence n hn)

end SymmetricSubgroupAsymptotics.BinarySmallOrbit16SevenDirect

end
