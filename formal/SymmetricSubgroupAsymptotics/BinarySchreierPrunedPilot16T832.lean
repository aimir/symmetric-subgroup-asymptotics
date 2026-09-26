import SymmetricSubgroupAsymptotics.BinarySchreierPrunedAdapter
import SymmetricSubgroupAsymptotics.GeneratedSchreierActions.Binding16T832
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.Order16T624

/-!
# A stopped two-source Schreier pilot on the original sixteen points

The original 16T832 source has two accepted membership assignments, both
bound by literal generator words to 16T624, with their original conjugators.
The other assignments are intransitive or trivial. A separately checked
order bound for the literal 16T624 source stops its index-two children at 128.

This installs the selected local bindings only. It neither identifies a
Sylow root nor claims a complete transitive-action or normal-entry registry.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySchreierPrunedPilot16T832

def catalogueIndex (i : Fin 2) : Fin 1427 :=
  if i.val = 0 then BinarySchreierBinding16T832.sourceIndex else 560

def actions (i : Fin 2) : Subgroup (Equiv.Perm (Fin 16)) :=
  BinaryActionData16.actions (catalogueIndex i)

theorem actions_eq_catalogue (i : Fin 2) :
    actions i = BinaryActionData16.actions (catalogueIndex i) := rfl

theorem source_eq : actions 0 =
    Subgroup.closure (Set.range BinarySchreierChildren16T832.generators) :=
  BinarySchreierBinding16T832.source_eq

theorem action_one_eq : actions 1 = BinaryPrunedOrder16T624.Original := rfl

private def sourceBinding : BinarySchreierPrunedBinding actions 128 0 :=
  .schreier 1 BinarySchreierChildren16T832.targets
    (by
      rw [source_eq]
      exact BinarySchreierChildren16T832.children)
    (Fin.cases (Or.inr ⟨1, BinarySchreierBinding16T832.target_eq 0⟩)
      (fun i => Fin.elim0 i))

private def boundary624 : BinarySchreierPrunedBinding actions 128 1 :=
  .boundary (by
    change Nat.card BinaryPrunedOrder16T624.Original ≤ 256
    exact BinaryPrunedOrder16T624.card_le)

/-- A word certificate and an actual order stop cover the two retained
original source indices, without a catalogue-order assumption. -/
def bindings : ∀ i, BinarySchreierPrunedBinding actions 128 i :=
  Fin.cases sourceBinding (Fin.cases boundary624 (fun i => Fin.elim0 i))

theorem children (i : Fin 2) :
    BinaryActionChildrenCoveredAboveOrder actions 128 (actions i) :=
  (bindings i).children

end SymmetricSubgroupAsymptotics.BinarySchreierPrunedPilot16T832

end
