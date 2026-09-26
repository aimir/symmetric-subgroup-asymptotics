import SymmetricSubgroupAsymptotics.BinarySmallOrbit16Physical
import SymmetricSubgroupAsymptotics.BinaryOrderCharacterDirectFusion

/-! Direct forward counting for the complete actual small-order
degree-sixteen orbit sector. Both coverage and naturality are proved.
There is no coarse subgroup-count premise or additive hot error. The
named character class-count input is retained in the counting theorem.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter

namespace SymmetricSubgroupAsymptotics.BinarySmallOrbit16Physical

open BinaryTransitiveBoundary16Fusion

/-- The complete original-action/normal row, whose target includes the
actual even graph prefix. No choice of physical orbit is counted twice
as a separate marked subgroup in the family on the left. -/
def directRow (n m : ℕ) : ℝ :=
  binaryOrderCharacterDirectRow (fun _ : BoundaryAction => 8) boundaryAction
    (menuSelection boundaryAction boundaryAction_transitive boundaryAction_card_le) n m

/-- All actual subgroups in this sector enter the same complete forward
row. No physical cover, count bound, or coarse-growth hypothesis is an input. -/
theorem direct_recurrence (hMaroti : NilpotentConjugacyClassInput)
    (n : ℕ) (hn : 16 ≤ n) :
    (Nat.card (physicalFamily n) : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ) / exactBenchmark m) :=
  binaryOrderCharacterSelection_direct_recurrence
    (fun _ : BoundaryAction => 8) boundaryAction
    (menuSelection boundaryAction boundaryAction_transitive boundaryAction_card_le)
    hMaroti boundaryAction_isPGroup (fun _ => by change 0 < 8; decide)
    n (fun _ => hn) (physicalFamily n) (fun _ _ => True)
    (fun _ _ _ _ => trivial) (cover hn)

theorem directRow_nonneg (n m : ℕ) : 0 ≤ directRow n m :=
  binaryOrderCharacterDirectRow_nonneg (fun _ : BoundaryAction => 8) boundaryAction
    (menuSelection boundaryAction boundaryAction_transitive boundaryAction_card_le) n m

theorem directRow_forward {n m : ℕ} (hnm : n ≤ m) : directRow n m = 0 :=
  binaryOrderCharacterDirectRow_forward (fun _ : BoundaryAction => 8) boundaryAction
    (menuSelection boundaryAction boundaryAction_transitive boundaryAction_card_le)
    (fun _ => by change 0 < 8; decide) hnm

/-- Exponential decay of the exact aggregate precedes any estimate on
the complete ordinary subgroup sequence. -/
theorem directRow_decay :
    ∃ A κ : ℝ, 0<A ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, directRow n m ≤ A*(2:ℝ)^(-κ*(n:ℝ)) :=
  binaryOrderCharacterDirectRow_decay (fun _ : BoundaryAction => 8) boundaryAction
    (menuSelection boundaryAction boundaryAction_transitive boundaryAction_card_le)
    (fun _ => by change 0 < 8; decide)

theorem directRow_contractive :
    ∀ᶠ n : ℕ in atTop, ∑ m ∈ Finset.range n, directRow n m ≤ 1/2 :=
  binaryOrderCharacterDirectRow_contractive (fun _ : BoundaryAction => 8) boundaryAction
    (menuSelection boundaryAction boundaryAction_transitive boundaryAction_card_le)
    (fun _ => by change 0 < 8; decide)

/-- Arbitrary earlier-owner exclusions only restrict the actual unmarked
sector; they introduce no extra multiplicity into the complete row. -/
theorem filtered_direct_recurrence (hMaroti : NilpotentConjugacyClassInput)
    (n : ℕ) (hn : 16 ≤ n) (R : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : physicalFamily n // R H.1} : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ) / exactBenchmark m) := by
  have hc : Nat.card {H : physicalFamily n // R H.1} ≤ Nat.card (physicalFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (direct_recurrence hMaroti n hn)

end SymmetricSubgroupAsymptotics.BinarySmallOrbit16Physical
