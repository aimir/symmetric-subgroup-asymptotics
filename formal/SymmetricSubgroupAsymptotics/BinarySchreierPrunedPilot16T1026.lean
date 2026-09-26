import SymmetricSubgroupAsymptotics.BinarySchreierPrunedAdapter
import SymmetricSubgroupAsymptotics.GeneratedSchreierActions.Binding16T1026
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.Order16T524
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.Order16T611

/-!
# A three-source stopped Schreier pilot on the original sixteen points

The retained sources are the literal common-family entries 16T1026, 16T524,
and 16T611. The existing checked 1026 local certificate supplies the two
targets with its original conjugators. Certified generator-edge order bounds
stop both target sources: their index-two children have order at most 128.

This supplies all local pruned bindings of this selected three-source family.
There is no claim that its first source is a Sylow subgroup, that this family
covers every transitive action, or that any carrier branch has been installed.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySchreierPrunedPilot16T1026

/-- The retained labels refer to the existing common original family. -/
def catalogueIndex (i : Fin 3) : Fin 1427 :=
  if i.val = 0 then BinarySchreierBinding16T1026.sourceIndex
  else if i.val = 1 then 460 else 547

def actions (i : Fin 3) : Subgroup (Equiv.Perm (Fin 16)) :=
  BinaryActionData16.actions (catalogueIndex i)

theorem actions_eq_catalogue (i : Fin 3) :
    actions i = BinaryActionData16.actions (catalogueIndex i) := rfl

theorem source_eq : actions 0 =
    Subgroup.closure (Set.range BinarySchreierChildren16T1026.generators) :=
  BinarySchreierBinding16T1026.source_eq

theorem action_one_eq : actions 1 = BinaryPrunedOrder16T524.Original := rfl

theorem action_two_eq : actions 2 = BinaryPrunedOrder16T611.Original := rfl

private def sourceBinding : BinarySchreierPrunedBinding actions 128 0 :=
  .schreier 2 BinarySchreierChildren16T1026.targets
    (by
      rw [source_eq]
      exact BinarySchreierChildren16T1026.children)
    (Fin.cases
      (Or.inr ⟨1, BinarySchreierBinding16T1026.target_eq 0⟩)
      (Fin.cases
        (Or.inr ⟨2, BinarySchreierBinding16T1026.target_eq 1⟩)
        (fun i => Fin.elim0 i)))

private def boundary524 : BinarySchreierPrunedBinding actions 128 1 :=
  .boundary (by
    change Nat.card BinaryPrunedOrder16T524.Original ≤ 256
    exact BinaryPrunedOrder16T524.card_le)

private def boundary611 : BinarySchreierPrunedBinding actions 128 2 :=
  .boundary (by
    change Nat.card BinaryPrunedOrder16T611.Original ≤ 256
    exact BinaryPrunedOrder16T611.card_le)

/-- Every retained source has an actual local word certificate or a proved
order stop. The order declarations in catalogue metadata are unused. -/
def bindings : ∀ i, BinarySchreierPrunedBinding actions 128 i :=
  Fin.cases sourceBinding
    (Fin.cases boundary524 (Fin.cases boundary611 (fun i => Fin.elim0 i)))

theorem children (i : Fin 3) :
    BinaryActionChildrenCoveredAboveOrder actions 128 (actions i) :=
  (bindings i).children

end SymmetricSubgroupAsymptotics.BinarySchreierPrunedPilot16T1026

end
