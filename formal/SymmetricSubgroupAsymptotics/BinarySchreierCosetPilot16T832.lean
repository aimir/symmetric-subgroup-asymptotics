import SymmetricSubgroupAsymptotics.BinarySchreierPrunedAssembly
import SymmetricSubgroupAsymptotics.GeneratedAction16.Data
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.CosetOrder16T832

/-!
# Original 16T832 order stop from a compressed coset certificate

The literal common-family source at index 698 has proved order at most 512.
Every index-two child therefore has order at most 256. No local Schreier
assignment enumeration is needed for this cap. The one-position slice below
does not identify a Sylow root or supply a complete action registry, and it
does not accept the source's own normal axes.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySchreierCosetPilot16T832

def sourceIndex : Fin 1427 := 698

theorem source_eq : BinaryActionData16.actions sourceIndex =
    BinaryPrunedCosetOrder16T832.Original := rfl

/-- The original source is stopped using its proved order, not its
catalogue order or a list of possible index-two membership assignments. -/
def binding : BinarySchreierPrunedBinding BinaryActionData16.actions 256 sourceIndex :=
  .boundary (by
    rw [source_eq]
    exact BinaryPrunedCosetOrder16T832.card_le)

theorem children : BinaryActionChildrenCoveredAboveOrder BinaryActionData16.actions 256
    (BinaryActionData16.actions sourceIndex) := binding.children

/-- A single checked position in the common-family assembly. All other
positions remain explicit obligations of any eventual full slice. -/
def singletonSlice : BinarySchreierPrunedBindingSlice BinaryActionData16.actions
    256 698 1 (by decide) := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact binding

end SymmetricSubgroupAsymptotics.BinarySchreierCosetPilot16T832

end
