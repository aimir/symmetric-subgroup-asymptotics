import SymmetricSubgroupAsymptotics.PermutationOrbitCoverGenerators
import Mathlib.GroupTheory.OrderOfElement

/-! A small cyclic point-orbit cover supplies the restricted Maschke bound. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {k G X : Type} [Field k] [Group G] [Finite G]
  [Fintype X] [DecidableEq X] [MulAction G X]

/-- For a finite permutation action, one invertible-order element and a
cover by its point orbits give a uniform module-generator bound. -/
theorem permutationFunctionRepresentation_uniform_of_cyclic_orbitCover
    (g : G) (horder : (orderOf g : k) ≠ 0)
    {n : ℕ} (representative : Fin n → X)
    (hcover : ∀ x : X, ∃ (j : Fin n) (m : ℕ), g ^ m • representative j = x) :
    UniformSubrepresentationGeneratorBound (permutationFunctionRepresentation k G X) n := by
  let L := Subgroup.zpowers g
  letI : NeZero (Nat.card L : k) := ⟨by
    simpa only [L, Nat.card_zpowers] using horder⟩
  apply permutationFunctionRepresentation_uniform_of_restricted_orbitCover
    L.subtype representative
  intro x
  obtain ⟨j, m, hm⟩ := hcover x
  exact ⟨j, ⟨g ^ m, Subgroup.npow_mem_zpowers g m⟩, hm⟩

end SymmetricSubgroupAsymptotics

end
