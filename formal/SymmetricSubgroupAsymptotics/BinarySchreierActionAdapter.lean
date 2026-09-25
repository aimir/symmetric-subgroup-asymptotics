import SymmetricSubgroupAsymptotics.BinarySylowCoverage

/-!
# Typed installation of local original-action Schreier certificates

The local source and every local target are bound to the common family by
literal subgroup equalities. No source order, target order, row table, or
catalogue-completeness assertion is part of the interface.
-/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

variable {w : ℕ} {I : Type*}

/-- The exact local-child interface used by the global Sylow argument. -/
def BinaryActionChildrenCovered
    (actions : I → Subgroup (Equiv.Perm (Fin w)))
    (source : Subgroup (Equiv.Perm (Fin w))) : Prop :=
  ∀ K : Subgroup (Equiv.Perm (Fin w)), K ≤ source → K.relIndex source=2 →
    PermutationSubgroupTransitive K → ActionRegistryCovered actions K

/-- A checked local source, its literal local targets, and exact bindings
into the original common action family. The local coverage proof may be
supplied independently by a word-sized Schreier module. -/
structure BinarySchreierActionBinding
    (actions : I → Subgroup (Equiv.Perm (Fin w))) (sourceIndex : I) where
  generatorCount : ℕ
  generators : Fin generatorCount → Equiv.Perm (Fin w)
  source_eq : actions sourceIndex=Subgroup.closure (Set.range generators)
  targetCount : ℕ
  targets : Fin targetCount → Subgroup (Equiv.Perm (Fin w))
  targetIndex : Fin targetCount → I
  target_eq : ∀ j, targets j=actions (targetIndex j)
  local_children : BinaryActionChildrenCovered targets
    (Subgroup.closure (Set.range generators))

namespace BinarySchreierActionBinding

variable {actions : I → Subgroup (Equiv.Perm (Fin w))} {sourceIndex : I}

/-- Source and target bindings preserve the actual subgroup `K` and the
ambient point conjugator produced by the local Schreier certificate. -/
theorem children (B : BinarySchreierActionBinding actions sourceIndex) :
    BinaryActionChildrenCovered actions (actions sourceIndex) := by
  intro K hle hindex htrans
  have hle' : K ≤ Subgroup.closure (Set.range B.generators) := by
    rw [← B.source_eq]
    exact hle
  have hi' : K.relIndex (Subgroup.closure (Set.range B.generators))=2 := by
    rw [← B.source_eq]
    exact hindex
  obtain ⟨j,g,hg⟩ := B.local_children K hle' hi' htrans
  exact ⟨B.targetIndex j,g,hg.trans (B.target_eq j)⟩

end BinarySchreierActionBinding

/-- Assemble bounded consecutive slices of the common action family.
This combines proof functions without expanding one global finite case split. -/
theorem binaryActionChildrenCovered_add {m n : ℕ}
    (actions : Fin (m+n) → Subgroup (Equiv.Perm (Fin w)))
    (left : ∀ i : Fin m, BinaryActionChildrenCovered actions (actions (Fin.castAdd n i)))
    (right : ∀ j : Fin n, BinaryActionChildrenCovered actions (actions (Fin.natAdd m j))) :
    ∀ i, BinaryActionChildrenCovered actions (actions i) :=
  Fin.addCases left right

/-- An actual Sylow root and installed local child proofs imply global
coverage of the original transitive binary permutation actions. -/
theorem binary_schreier_action_registry_complete
    (actions : I → Subgroup (Equiv.Perm (Fin w)))
    (P : Sylow 2 (Equiv.Perm (Fin w))) (root : I)
    (hroot : actions root=(P : Subgroup (Equiv.Perm (Fin w))))
    (children : ∀ i, BinaryActionChildrenCovered actions (actions i))
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : IsPGroup 2 H)
    (ht : PermutationSubgroupTransitive H) : ActionRegistryCovered actions H :=
  permutation_pGroup_action_registry_complete actions P root hroot
    (fun i K hlt hindex htrans => children i K hlt.le hindex htrans) H hH ht

/-- The same adapter accepts one typed local binding per common source. -/
theorem binary_schreier_action_registry_complete_of_bindings
    (actions : I → Subgroup (Equiv.Perm (Fin w)))
    (P : Sylow 2 (Equiv.Perm (Fin w))) (root : I)
    (hroot : actions root=(P : Subgroup (Equiv.Perm (Fin w))))
    (bindings : ∀ i, BinarySchreierActionBinding actions i)
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : IsPGroup 2 H)
    (ht : PermutationSubgroupTransitive H) : ActionRegistryCovered actions H :=
  binary_schreier_action_registry_complete actions P root hroot
    (fun i => (bindings i).children) H hH ht

end SymmetricSubgroupAsymptotics
