import SymmetricSubgroupAsymptotics.CliffordRestriction

/-! Ambient conjugation transports the actual isotypic components of a
normal restriction. This supplies the canonical block permutation without
choosing invariant complements or changing the original module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGCliffordIsotypicTransport

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal]

abbrev restricted : Representation k H V := rho.comp H.subtype

def latticeConjugation (g : G) :
    Submodule k[H] (restricted rho H).asModule ≃o
      Submodule k[H] (restricted rho H).asModule :=
  Subrepresentation.subrepresentationSubmoduleOrderIso.symm.trans
    ((Theory.Representation.conjugateSubrepresentationOrderIso rho H g).trans
      Subrepresentation.subrepresentationSubmoduleOrderIso)

theorem latticeConjugation_one
    (S : Submodule k[H] (restricted rho H).asModule) :
    latticeConjugation rho H 1 S = S := by
  change Subrepresentation.subrepresentationSubmoduleOrderIso
      (Theory.Representation.conjugateSubrepresentationOrderIso rho H 1
        (Subrepresentation.subrepresentationSubmoduleOrderIso.symm S)) = S
  rw [Theory.Representation.conjugateSubrepresentationOrderIso_one]
  exact OrderIso.apply_symm_apply _ _

theorem latticeConjugation_mul (g h : G)
    (S : Submodule k[H] (restricted rho H).asModule) :
    latticeConjugation rho H (g * h) S =
      latticeConjugation rho H g (latticeConjugation rho H h S) := by
  simp only [latticeConjugation, OrderIso.trans_apply, OrderIso.symm_apply_apply,
    Theory.Representation.conjugateSubrepresentationOrderIso_mul]

theorem conjugation_preserves_isomorphism (g : G)
    (S T : Submodule k[H] (restricted rho H).asModule)
    (h : Nonempty (S ≃ₗ[k[H]] T)) :
    Nonempty (latticeConjugation rho H g S ≃ₗ[k[H]] latticeConjugation rho H g T) := by
  let e : Subrepresentation (restricted rho H) ≃o
      Submodule k[H] (restricted rho H).asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  let U := e.symm S
  let W := e.symm T
  have hUW : Nonempty (U.asSubmodule ≃ₗ[k[H]] W.asSubmodule) := by
    change Nonempty (e (e.symm S) ≃ₗ[k[H]] e (e.symm T))
    simpa only [e.apply_symm_apply] using h
  obtain ⟨f⟩ :=
    (Theory.Representation.isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv U W).mpr hUW
  change Nonempty ((Theory.Representation.conjugateSubrepresentationOrderIso rho H g U).asSubmodule ≃ₗ[k[H]]
    (Theory.Representation.conjugateSubrepresentationOrderIso rho H g W).asSubmodule)
  exact (Theory.Representation.isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv _ _).mp
    ⟨Theory.Representation.conjugateSubrepresentationOrderIsoRepEquiv rho H f g⟩

theorem conjugation_isomorphism_iff (g : G)
    (S T : Submodule k[H] (restricted rho H).asModule) :
    Nonempty (latticeConjugation rho H g S ≃ₗ[k[H]] latticeConjugation rho H g T) ↔
      Nonempty (S ≃ₗ[k[H]] T) := by
  constructor
  · intro h
    have hi := conjugation_preserves_isomorphism rho H g⁻¹ _ _ h
    have hinv (X : Submodule k[H] (restricted rho H).asModule) :
        latticeConjugation rho H g⁻¹ (latticeConjugation rho H g X) = X := by
      calc
        _ = latticeConjugation rho H (g⁻¹ * g) X :=
          (latticeConjugation_mul rho H g⁻¹ g X).symm
        _ = latticeConjugation rho H 1 X := by rw [inv_mul_cancel]
        _ = X := latticeConjugation_one rho H X
    exact ⟨((LinearEquiv.ofEq _ _ (hinv S)).symm.trans hi.some).trans
      (LinearEquiv.ofEq _ _ (hinv T))⟩
  · exact conjugation_preserves_isomorphism rho H g S T

theorem latticeConjugation_isotypicComponent (g : G)
    (S : Submodule k[H] (restricted rho H).asModule) :
    latticeConjugation rho H g (isotypicComponent k[H] (restricted rho H).asModule S) =
      isotypicComponent k[H] (restricted rho H).asModule (latticeConjugation rho H g S) := by
  let e := latticeConjugation rho H g
  have hset : e '' {T : Submodule k[H] (restricted rho H).asModule |
      Nonempty (T ≃ₗ[k[H]] S)} =
      {T : Submodule k[H] (restricted rho H).asModule |
        Nonempty (T ≃ₗ[k[H]] e S)} := by
    apply Set.ext
    intro T
    constructor
    · rintro ⟨W, hW, rfl⟩
      exact conjugation_preserves_isomorphism rho H g W S hW
    · intro hT
      refine ⟨e.symm T, ?_, e.apply_symm_apply T⟩
      apply (conjugation_isomorphism_iff rho H g (e.symm T) S).mp
      change Nonempty (e (e.symm T) ≃ₗ[k[H]] e S)
      exact ⟨(LinearEquiv.ofEq _ _ (e.apply_symm_apply T)).trans hT.some⟩
  change e (sSup {T : Submodule k[H] (restricted rho H).asModule |
    Nonempty (T ≃ₗ[k[H]] S)}) =
    sSup {T : Submodule k[H] (restricted rho H).asModule |
      Nonempty (T ≃ₗ[k[H]] e S)}
  rw [e.map_sSup, ← sSup_image, hset]

end SymmetricSubgroupAsymptotics.CFSGCliffordIsotypicTransport
