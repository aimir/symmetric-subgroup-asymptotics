import SymmetricSubgroupAsymptotics.BinarySchreierPrunedAssembly
import SymmetricSubgroupAsymptotics.BinarySchreierEncodedOrderStops
import SymmetricSubgroupAsymptotics.GeneratedSchreierActions.Binding16T1025
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.Order16T473
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.Order16T485
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.Order16T500
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.Order16T510
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.Order16T590
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.Order16T633

/-! A selected seven-source order-pruned Schreier family on the original
sixteen points. The existing complete 16T1025 local certificate supplies
its six targets with the same original generator tuples and conjugators.
Each target source is stopped by a separate actual order bound of 256,
so its index-two children have order at most 128.

This proves the local bindings of this selected family only. No member is
asserted to be a Sylow root, and there is no claim of global transitive
coverage, carrier coverage, or source acceptance from catalogue metadata.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySchreierPrunedPilot16T1025

/-- Keep the source and every target's existing common-family index. -/
def catalogueIndex : Fin 7 → Fin 1427 :=
  Fin.cases BinarySchreierBinding16T1025.sourceIndex BinarySchreierBinding16T1025.targetIndex

def actions (i : Fin 7) : Subgroup (Equiv.Perm (Fin 16)) :=
  BinaryActionData16.actions (catalogueIndex i)

theorem actions_eq_catalogue (i : Fin 7) :
    actions i = BinaryActionData16.actions (catalogueIndex i) := rfl

theorem source_eq : actions 0 =
    Subgroup.closure (Set.range BinarySchreierChildren16T1025.generators) :=
  BinarySchreierBinding16T1025.source_eq

/-- Every existing local target has its own unchanged position in this
selected family; none is replaced by an order-only label. -/
theorem target_eq (j : Fin 6) :
    BinarySchreierChildren16T1025.targets j = actions j.succ :=
  BinarySchreierBinding16T1025.target_eq j

theorem action_473_eq : actions 1 = BinaryPrunedOrder16T473.Original := rfl

theorem action_485_eq : actions 2 = BinaryPrunedOrder16T485.Original := rfl

theorem action_500_eq : actions 3 = BinaryPrunedOrder16T500.Original := rfl

theorem action_510_eq : actions 4 = BinaryPrunedOrder16T510.Original := rfl

theorem action_590_eq : actions 5 = BinaryPrunedOrder16T590.Original := rfl

theorem action_633_eq : actions 6 = BinaryPrunedOrder16T633.Original := rfl

private def sourceBinding : BinarySchreierPrunedBinding actions 128 0 :=
  .schreier 6 BinarySchreierChildren16T1025.targets
    (by
      rw [source_eq]
      exact BinarySchreierChildren16T1025.children)
    (fun j => Or.inr ⟨j.succ, target_eq j⟩)

private def boundaryOrder16T473 : BinarySchreierPrunedBinding actions 128 1 :=
  .ofEncodedCayley BinaryPrunedOrder16T473.generators
    BinaryPrunedOrder16T473.certificate action_473_eq (by decide)

private def boundaryOrder16T485 : BinarySchreierPrunedBinding actions 128 2 :=
  .ofEncodedCayley BinaryPrunedOrder16T485.generators
    BinaryPrunedOrder16T485.certificate action_485_eq (by decide)

private def boundaryOrder16T500 : BinarySchreierPrunedBinding actions 128 3 :=
  .ofEncodedCayley BinaryPrunedOrder16T500.generators
    BinaryPrunedOrder16T500.certificate action_500_eq (by decide)

private def boundaryOrder16T510 : BinarySchreierPrunedBinding actions 128 4 :=
  .ofEncodedCayley BinaryPrunedOrder16T510.generators
    BinaryPrunedOrder16T510.certificate action_510_eq (by decide)

private def boundaryOrder16T590 : BinarySchreierPrunedBinding actions 128 5 :=
  .ofEncodedCayley BinaryPrunedOrder16T590.generators
    BinaryPrunedOrder16T590.certificate action_590_eq (by decide)

private def boundaryOrder16T633 : BinarySchreierPrunedBinding actions 128 6 :=
  .ofEncodedCayley BinaryPrunedOrder16T633.generators
    BinaryPrunedOrder16T633.certificate action_633_eq (by decide)

/-- All seven source bindings are proved from actual local certificates
or actual source order bounds. The declared catalogue orders are unused. -/
def bindings : ∀ i, BinarySchreierPrunedBinding actions 128 i :=
  Fin.cases sourceBinding
    (Fin.cases boundaryOrder16T473 (Fin.cases boundaryOrder16T485 (Fin.cases boundaryOrder16T500 (Fin.cases boundaryOrder16T510 (Fin.cases boundaryOrder16T590 (Fin.cases boundaryOrder16T633 (fun i => Fin.elim0 i)))))))

theorem children (i : Fin 7) :
    BinaryActionChildrenCoveredAboveOrder actions 128 (actions i) :=
  (bindings i).children

/-- The bounded assembly interface contains all seven literal positions. -/
def fullSlice : BinarySchreierPrunedBindingSlice actions 128 0 7 (by omega) := by
  intro i
  simpa only [binarySchreierBindingIndex, Nat.zero_add] using bindings i

end SymmetricSubgroupAsymptotics.BinarySchreierPrunedPilot16T1025
