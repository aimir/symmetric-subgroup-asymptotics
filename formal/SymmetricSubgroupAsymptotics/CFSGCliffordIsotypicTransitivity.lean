import SymmetricSubgroupAsymptotics.CFSGCliffordIsotypicPermutation

/-! Clifford conjugacy makes the canonical component permutation transitive.
The components and their permutation are those of the original restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGCliffordIsotypicTransitivity
open CFSGCliffordIsotypicTransport CFSGCliffordIsotypicPermutation

variable {k G V : Type} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (rho : Representation k G V) (hrho : Representation.IsIrreducible rho)
  (H : Subgroup G) [H.Normal]

include hrho in
theorem exists_component_transport (C D : Components rho H) :
    ∃ g : G, componentMap rho H g C = D := by
  obtain ⟨S, hs, hC⟩ := C.property
  obtain ⟨T, ht, hD⟩ := D.property
  let e : Subrepresentation (restricted rho H) ≃o
      Submodule k[H] (restricted rho H).asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  let U := e.symm S
  let W := e.symm T
  have hU : Representation.IsIrreducible U.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom U).mpr
    apply (e.isAtom_iff U).mp
    change IsAtom (e (e.symm S))
    simpa only [e.apply_symm_apply] using isSimpleModule_iff_isAtom.mp hs
  have hW : Representation.IsIrreducible W.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom W).mpr
    apply (e.isAtom_iff W).mp
    change IsAtom (e (e.symm T))
    simpa only [e.apply_symm_apply] using isSimpleModule_iff_isAtom.mp ht
  obtain ⟨g, ⟨f⟩⟩ :=
    CliffordRawRestriction.proved.conjugateTypes rho hrho H U W hU hW
  let f' : Theory.Representation.conjugateRep (G := G) (H := H)
      U.toRepresentation g ≃ₗ W.toRepresentation :=
    Theory.Representation.RepEquiv.ofRepresentationEquiv f
  let fg := (Theory.Representation.conjugateSubrepresentationEquiv rho H U g).trans f'
  have he : Nonempty (latticeConjugation rho H g⁻¹ S ≃ₗ[k[H]] T) := by
    have hleft : latticeConjugation rho H g⁻¹ S =
        (Theory.Representation.conjugateSubrepresentation rho H U g).asSubmodule := by
      change (Theory.Representation.conjugateSubrepresentation rho H U (g⁻¹)⁻¹).asSubmodule = _
      rw [inv_inv]
    have hright : W.asSubmodule = T := e.apply_symm_apply T
    have hfg :=
      (Theory.Representation.isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv
        _ _).mp ⟨fg⟩
    exact ⟨(LinearEquiv.ofEq _ _ hleft).trans
      (hfg.some.trans (LinearEquiv.ofEq _ _ hright))⟩
  refine ⟨g⁻¹, ?_⟩
  apply Subtype.ext
  change latticeConjugation rho H g⁻¹ C.val = D.val
  rw [hC, hD, latticeConjugation_isotypicComponent]
  exact he.some.isotypicComponent_eq

end SymmetricSubgroupAsymptotics.CFSGCliffordIsotypicTransitivity
