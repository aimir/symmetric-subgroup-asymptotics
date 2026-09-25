import SymmetricSubgroupAsymptotics.BinarySchreierActionAdapter
import SymmetricSubgroupAsymptotics.GeneratedAction16.Data
import SymmetricSubgroupAsymptotics.BinaryMenuRoots

/-!
# Original degree-sixteen family and its actual Sylow root

Only the existing original generator tuples and structural Sylow proof are
imported. No legacy source-element certificate or old aggregate proof DAG
is imported. Global completion still requires every local child proof.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySchreierAction16

abbrev actions := BinaryActionData16.actions

/-- The common family's retained original `b16_1823` source. -/
def rootIndex : Fin 1427 := 1426

theorem root_generators_eq :
    BinaryActionData16.node1823Generators=BinaryMenuRoot16.generators := by
  decide +kernel

/-- This is the actual original Sylow subgroup, including the point
conjugator already checked by `BinaryMenuRoot16`. -/
theorem root_eq : actions rootIndex=
    (BinaryMenuRoot16.sylow : Subgroup (Equiv.Perm (Fin 16))) := by
  rw [BinaryMenuRoot16.sylow_eq]
  change Subgroup.closure (Set.range BinaryActionData16.node1823Generators)=_
  rw [root_generators_eq]

/-- Integration boundary: every common-family source still requires its
checked local child theorem. This is not an installed aggregate certificate. -/
theorem complete_of_local_checks
    (children : ∀ i, BinaryActionChildrenCovered actions (actions i))
    (H : Subgroup (Equiv.Perm (Fin 16))) (hH : IsPGroup 2 H)
    (ht : PermutationSubgroupTransitive H) : ActionRegistryCovered actions H :=
  binary_schreier_action_registry_complete actions BinaryMenuRoot16.sylow
    rootIndex root_eq children H hH ht

theorem complete_of_bindings
    (bindings : ∀ i, BinarySchreierActionBinding actions i)
    (H : Subgroup (Equiv.Perm (Fin 16))) (hH : IsPGroup 2 H)
    (ht : PermutationSubgroupTransitive H) : ActionRegistryCovered actions H :=
  complete_of_local_checks (fun i => (bindings i).children) H hH ht

end SymmetricSubgroupAsymptotics.BinarySchreierAction16
