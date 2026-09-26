import SymmetricSubgroupAsymptotics.BinaryTransitiveBoundary16Fusion
import SymmetricSubgroupAsymptotics.FusionPhysicalCharts

/-! The actual physical family with a transitive binary orbit of degree
sixteen and order at most 256. Its complete restriction image is computed
from an original point chart. The coverage proof is supplied here, not
assumed as a numerical or canonical-family membership premise.

All other orbits and their correlations remain in the complete complement.
The class-count input remains explicit, as does the separate coarse input
when estimating the hot error. This is one sector of the ordinary count.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter

namespace SymmetricSubgroupAsymptotics.BinarySmallOrbit16Physical

open BinaryTransitiveBoundary16Fusion

/-- The literal first restriction image in a chosen physical chart. -/
def orbitAction {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (e : Fin 16 ⊕ Fin (n-16) ≃ Fin n) : Subgroup (Equiv.Perm (Fin 16)) :=
  (fusionPhysicalBlockPullback (relabelSubgroup e.symm H)).map
    (MonoidHom.fst (Equiv.Perm (Fin 16)) (Equiv.Perm (Fin (n-16))))

/-- Geometric and algebraic data on the actual subgroup. Transitivity of
the full restriction image makes the invariant block one genuine orbit. -/
structure OrbitChart {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) where
  chart : Fin 16 ⊕ Fin (n-16) ≃ Fin n
  preserves : ∀ k ∈ relabelSubgroup chart.symm H,
    Set.MapsTo k (Set.range (Sum.inl : Fin 16 → Fin 16 ⊕ Fin (n-16)))
      (Set.range (Sum.inl : Fin 16 → Fin 16 ⊕ Fin (n-16)))
  binary : IsPGroup 2 (orbitAction H chart)
  transitive : MulAction.IsPretransitive (orbitAction H chart) (Fin 16)
  order_le : Nat.card (orbitAction H chart) ≤ 256

/-- The chart's first block is an actual orbit of the original subgroup
in these coordinates, rather than a union of smaller orbits. -/
theorem OrbitChart.orbit_eq {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (C : OrbitChart H) (x : Fin 16) :
    MulAction.orbit (relabelSubgroup C.chart.symm H) (Sum.inl x) =
      Set.range (Sum.inl : Fin 16 → Fin 16 ⊕ Fin (n-16)) := by
  let U := orbitAction H C.chart
  let K := relabelSubgroup C.chart.symm H
  letI : MulAction.IsPretransitive U (Fin 16) := C.transitive
  have ht (a b : Fin 16) : ∃ u : U, (u : Equiv.Perm (Fin 16)) a = b :=
    MulAction.exists_smul_eq U a b
  have hf := fusionDeletedModel_full U K rfl
  have hr := fusionDeletedModel_recovers U K C.preserves rfl
  have ho := fusionOrbitAction_orbit_eq U ht ⟨fusionDeletedModel U K, hf⟩ x
  exact (congrArg (fun L : Subgroup (Equiv.Perm (Fin 16 ⊕ Fin (n-16))) =>
    MulAction.orbit L (Sum.inl x)) hr).symm.trans ho

/-- An unmarked family of actual subgroups. Existence of a chart does
not charge the number of choices of a distinguished orbit or its labels. -/
def physicalFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | Nonempty (OrbitChart H)}

/-- The exact restriction image chooses its entry in the complete
finite accepted-action subtype; no catalogue representative is selected. -/
theorem cover {n : ℕ} (hn : 16 ≤ n)
    (H : Subgroup (Equiv.Perm (Fin n))) (hH : H ∈ physicalFamily n) :
    ∃ i : BoundaryAction,
      H ∈ FusionCanonicalFamily (h := 8) (boundaryAction i) hn (fun _ => True) := by
  obtain ⟨C⟩ := hH
  let i : BoundaryAction := ⟨orbitAction H C.chart, C.binary, C.transitive, C.order_le⟩
  refine ⟨i, ?_⟩
  exact fusionCanonicalFamily_of_chart (h := 8) (boundaryAction i) hn H C.chart
    C.preserves rfl (fun _ => True) trivial

/-- Complete original-weight recurrence on this intrinsic physical
sector. Its naturality and physical coverage are proved, not hypotheses. -/
theorem recurrence (hMaroti : NilpotentConjugacyClassInput) (n : ℕ) (hn : 16 ≤ n) :
    (Nat.card (physicalFamily n) : ℝ) / exactBenchmark n ≤
      allActionsHot n + ∑ b ∈ Finset.range n, allActionsRow n b *
        ((subgroupCount b : ℝ) / exactBenchmark b) :=
  all_actions_recurrence hMaroti n hn (physicalFamily n) (fun _ _ => True)
    (fun _ _ _ _ => trivial) (cover hn)

/-- Restricting this actual sector by an earlier-owner or noncritical
predicate can only decrease its unmarked cardinality. -/
theorem filtered_recurrence (hMaroti : NilpotentConjugacyClassInput)
    (n : ℕ) (hn : 16 ≤ n) (R : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : physicalFamily n // R H.1} : ℝ) / exactBenchmark n ≤
      allActionsHot n + ∑ b ∈ Finset.range n, allActionsRow n b *
        ((subgroupCount b : ℝ) / exactBenchmark b) := by
  have hc : Nat.card {H : physicalFamily n // R H.1} ≤ Nat.card (physicalFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (recurrence hMaroti n hn)

/-- The installed continuation row is the same complete finite row
already proved to contract, without assuming bounded ordinary counts. -/
theorem row_contractive :
    ∀ᶠ n : ℕ in atTop, ∑ b ∈ Finset.range n, allActionsRow n b ≤ 1/2 :=
  all_actions_row_contractive

theorem hot_decay (hs : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ∃ D κ : ℝ, 0<D ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      allActionsHot n ≤ D*(2:ℝ)^(-κ*(n:ℝ)^2) :=
  all_actions_hot_decay hs

end SymmetricSubgroupAsymptotics.BinarySmallOrbit16Physical
