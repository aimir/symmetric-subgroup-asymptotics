import SymmetricSubgroupAsymptotics.BinaryOrderPrunedCoverage
import SymmetricSubgroupAsymptotics.BinarySchreierActionAdapter

/-! Local Schreier certificates with proved order stops.

Existing complete word certificates can be reused without changing their
generators or conjugators. Each literal target is either bounded in order
or bound to the retained family. A source of order at most twice the cap
needs no child certificate, because every index-two child is already small.
Declared catalogue orders are not accepted as evidence for either bound.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics

variable {w : ℕ} {I : Type*}

def BinaryActionChildrenCoveredAboveOrder
    (actions : I → Subgroup (Equiv.Perm (Fin w))) (cap : ℕ)
    (source : Subgroup (Equiv.Perm (Fin w))) : Prop :=
  ∀ K : Subgroup (Equiv.Perm (Fin w)), K ≤ source → K.relIndex source = 2 →
    PermutationSubgroupTransitive K → cap < Nat.card K →
      ActionRegistryCovered actions K

/-- A checked upper bound on the literal source stops all index-two
children at once. No membership assignments need to be enumerated. -/
theorem binaryActionChildrenAboveOrder_of_card_le_twice
    (actions : I → Subgroup (Equiv.Perm (Fin w))) (cap : ℕ)
    (source : Subgroup (Equiv.Perm (Fin w)))
    (hcard : Nat.card source ≤ 2*cap) :
    BinaryActionChildrenCoveredAboveOrder actions cap source := by
  intro K hK hindex _ hlarge
  have hc := (K.subgroupOf source).card_mul_index
  have he : Nat.card (K.subgroupOf source) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  change (K.subgroupOf source).index = 2 at hindex
  rw [he, hindex] at hc
  omega

/-- The exact old local conjugacy certificate remains usable. Only the
finite target resolution changes, and a small target contradicts the
retained actual child's order. -/
theorem binaryActionChildrenAboveOrder_of_local_targets
    {κ : Type*} (actions : I → Subgroup (Equiv.Perm (Fin w))) (cap : ℕ)
    (source : Subgroup (Equiv.Perm (Fin w)))
    (targets : κ → Subgroup (Equiv.Perm (Fin w)))
    (hlocal : BinaryActionChildrenCovered targets source)
    (htargets : ∀ j, Nat.card (targets j) ≤ cap ∨
      ActionRegistryCovered actions (targets j)) :
    BinaryActionChildrenCoveredAboveOrder actions cap source := by
  intro K hK hindex htrans hlarge
  obtain ⟨j, g, hg⟩ := hlocal K hK hindex htrans
  have hc : Nat.card K = Nat.card (targets j) := by
    calc
      Nat.card K = Nat.card ↥(MulAut.conj g • K) :=
        Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) K).toEquiv
      _ = Nat.card (targets j) :=
        congrArg (fun V : Subgroup (Equiv.Perm (Fin w)) => Nat.card V) hg
  rcases htargets j with hsmall | hcovered
  · omega
  · apply actionRegistryCovered_of_conjugate actions g K
    rwa [hg]

/-- Finite local inputs for a retained original source. Boundary proofs
and word certificates are kept separate; neither constructor assumes
global coverage or a catalogue cardinality. -/
inductive BinarySchreierPrunedBinding
    (actions : I → Subgroup (Equiv.Perm (Fin w))) (cap : ℕ) (sourceIndex : I) : Type
  | boundary (card_le : Nat.card (actions sourceIndex) ≤ 2*cap)
  | schreier (targetCount : ℕ)
      (targets : Fin targetCount → Subgroup (Equiv.Perm (Fin w)))
      (local_children : BinaryActionChildrenCovered targets (actions sourceIndex))
      (target_resolution : ∀ j, Nat.card (targets j) ≤ cap ∨
        ∃ i, targets j = actions i)

namespace BinarySchreierPrunedBinding

variable {actions : I → Subgroup (Equiv.Perm (Fin w))} {cap : ℕ} {sourceIndex : I}

theorem children (B : BinarySchreierPrunedBinding actions cap sourceIndex) :
    BinaryActionChildrenCoveredAboveOrder actions cap (actions sourceIndex) := by
  cases B with
  | boundary hcard =>
    exact binaryActionChildrenAboveOrder_of_card_le_twice actions cap _ hcard
  | schreier targetCount targets hlocal htargets =>
    apply binaryActionChildrenAboveOrder_of_local_targets actions cap _ targets hlocal
    intro j
    rcases htargets j with hsmall | ⟨i, hi⟩
    · exact Or.inl hsmall
    · exact Or.inr ⟨i, 1, by simpa only [map_one, one_smul] using hi⟩

end BinarySchreierPrunedBinding

/-- One local stopped certificate per retained action suffices. An actual
transitive binary action is either small or conjugate to a retained action. -/
theorem binary_schreier_pruned_registry_complete
    (actions : I → Subgroup (Equiv.Perm (Fin w))) (cap : ℕ)
    (P : Sylow 2 (Equiv.Perm (Fin w))) (root : I)
    (hroot : actions root = (P : Subgroup (Equiv.Perm (Fin w))))
    (bindings : ∀ i, BinarySchreierPrunedBinding actions cap i)
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : IsPGroup 2 H)
    (ht : PermutationSubgroupTransitive H) :
    Nat.card H ≤ cap ∨ ActionRegistryCovered actions H :=
  BinaryOrderPrunedCoverage.action_registry_complete_above_order
    actions P root hroot cap
    (fun i K hlt hindex htrans hlarge =>
      (bindings i).children K hlt.le hindex htrans hlarge) H hH ht

end SymmetricSubgroupAsymptotics

end
