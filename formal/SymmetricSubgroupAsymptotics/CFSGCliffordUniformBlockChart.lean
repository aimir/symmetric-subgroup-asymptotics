import SymmetricSubgroupAsymptotics.CFSGCliffordComponentDimensions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Dimension.Free

/-! A uniform literal block chart extracted from the canonical Clifford
components. Its permutation and coordinate-kernel condition are proved
from the original representation, rather than supplied as new premises. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGCliffordUniformBlockChart
open CFSGCliffordIsotypicTransport CFSGCliffordIsotypicPermutation
  CFSGCliffordComponentCoordinates CFSGCliffordComponentDimensions

variable {k G V : Type} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [Finite V] [FiniteDimensional k V]
  (rho : Representation k G V) (hrho : Representation.IsIrreducible rho)
  (H : Subgroup G) [H.Normal]

include hrho in
theorem exists_uniform_block_chart (C : Components rho H) :
    ∃ (e : V ≃ₗ[k]
        (Fin (Nat.card (Components rho H)) → Fin (Module.finrank k C.val) → k))
      (pi : G →* Equiv.Perm (Fin (Nat.card (Components rho H)))),
      ∀ (g : pi.ker) (v : V) (i : Fin (Nat.card (Components rho H))),
        e v i = 0 → e (rho g.val v) i = 0 := by
  letI : Finite (Components rho H) := components_finite rho H
  letI : Fintype (Components rho H) := Fintype.ofFinite _
  letI : ∀ D : Components rho H, FiniteDimensional k D.val := fun D =>
    FiniteDimensional.of_injective (D.val.subtype.restrictScalars k)
      D.val.subtype_injective
  let hss := CliffordRawRestriction.proved.semisimple rho hrho H
  let I := Components rho H
  let d := Module.finrank k C.val
  let rows (D : I) : D.val ≃ₗ[k] (Fin d → k) :=
    LinearEquiv.ofFinrankEq _ _ (by
      simpa only [Module.finrank_pi, Fintype.card_fin] using
        component_module_finrank_eq rho H hrho D C)
  let ei : I ≃ Fin (Nat.card I) := Finite.equivFin I
  let E : V ≃ₗ[k] (Fin (Nat.card I) → Fin d → k) :=
    (coordinates rho H hss).trans
      ((LinearEquiv.piCongrRight rows).trans
        (LinearEquiv.piCongrLeft' k (fun _ : I => Fin d → k) ei))
  let pi : G →* Equiv.Perm (Fin (Nat.card I)) :=
    ei.permCongrHom.toMonoidHom.comp (componentPermutationHom rho H)
  refine ⟨E, pi, ?_⟩
  intro g v i hv
  have hg : componentPermutationHom rho H g.val = 1 := by
    apply ei.permCongrHom.injective
    change pi g.val = ei.permCongrHom 1
    rw [MonoidHom.mem_ker.mp g.property, map_one]
  let g' : (componentPermutationHom rho H).ker := ⟨g.val, hg⟩
  have hv' : coordinates rho H hss v (ei.symm i) = 0 := by
    apply (rows (ei.symm i)).injective
    change rows (ei.symm i) (coordinates rho H hss v (ei.symm i)) =
      rows (ei.symm i) 0
    exact hv.trans (map_zero (rows (ei.symm i))).symm
  have hout := kernel_coordinate_zero rho H hss g' v (ei.symm i) hv'
  change rows (ei.symm i) (coordinates rho H hss (rho g.val v) (ei.symm i)) = 0
  rw [hout, map_zero]

end SymmetricSubgroupAsymptotics.CFSGCliffordUniformBlockChart
