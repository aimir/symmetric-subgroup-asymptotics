import SymmetricSubgroupAsymptotics.CFSGCliffordIsotypicTransitivity
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The canonical isotypic components as literal subspaces of the original
representation carrier. Ambient conjugation transports them by the actual
representation operator, so component dimensions are equal and the kernel
of the canonical permutation preserves each original subspace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGCliffordComponentSpaces
open CFSGCliffordIsotypicTransport CFSGCliffordIsotypicPermutation

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal]

def space (S : Submodule k[H] (restricted rho H).asModule) : Submodule k V :=
  (Subrepresentation.ofSubmodule' S).toSubmodule

theorem space_conjugation (g : G)
    (S : Submodule k[H] (restricted rho H).asModule) :
    space rho H (latticeConjugation rho H g S) = (space rho H S).map (rho g) := by
  change (Theory.Representation.conjugateSubrepresentationOrderIso rho H g
    (Subrepresentation.ofSubmodule' S)).toSubmodule =
      (Subrepresentation.ofSubmodule' S).toSubmodule.map (rho g)
  exact Theory.Representation.conjugateSubrepresentationOrderIso_toSubmodule rho H g _

theorem space_conjugation_finrank (g : G)
    (S : Submodule k[H] (restricted rho H).asModule) :
    Module.finrank k (space rho H (latticeConjugation rho H g S)) =
      Module.finrank k (space rho H S) := by
  rw [space_conjugation]
  exact (LinearEquiv.ofBijective (rho g) (Representation.apply_bijective rho g)).finrank_map_eq _

theorem kernel_preserves_space (g : G)
    (hg : g ∈ (componentPermutationHom rho H).ker) (C : Components rho H)
    (v : V) (hv : v ∈ space rho H C.val) : rho g v ∈ space rho H C.val := by
  have he : (space rho H C.val).map (rho g) = space rho H C.val := by
    rw [← space_conjugation, kernel_fixes_component rho H g hg C]
  rw [← he]
  exact ⟨v, hv, rfl⟩

theorem component_finrank_eq [Finite G] [FiniteDimensional k V]
    (hrho : Representation.IsIrreducible rho) (C D : Components rho H) :
    Module.finrank k (space rho H C.val) = Module.finrank k (space rho H D.val) := by
  obtain ⟨g, hg⟩ :=
    CFSGCliffordIsotypicTransitivity.exists_component_transport rho hrho H C D
  have he : latticeConjugation rho H g C.val = D.val := congrArg Subtype.val hg
  have hd := space_conjugation_finrank rho H g C.val
  rw [he] at hd
  exact hd.symm

end SymmetricSubgroupAsymptotics.CFSGCliffordComponentSpaces
