import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.Data.Fintype.Perm

/-! Native interface between actual transitive wreath-envelope construction
and the actual orbit-product cover. Both sides use literal labelled inclusion. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers

structure TransitiveSolubleContainerCover (n : ℕ) where
  Index : Type
  finiteIndex : Finite Index
  group : Index → Subgroup (Equiv.Perm (Fin n))
  soluble : ∀ i, IsSolvable (group i)
  covers : ∀ G : Subgroup (Equiv.Perm (Fin n)), IsSolvable G →
    MulAction.IsPretransitive G (Fin n) → ∃ i, G ≤ group i

attribute [instance] TransitiveSolubleContainerCover.finiteIndex

end SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
