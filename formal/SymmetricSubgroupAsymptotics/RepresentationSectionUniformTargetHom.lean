import SymmetricSubgroupAsymptotics.SchurSectionUniformTargetHom
import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads

/-! Representation adapter for the actual-isotypic-preimage section
argument. The input and output retain the displayed original quotient map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

/-- A bound for maps from every original subrepresentation to the same
simple target controls that type in every original quotient section. -/
theorem representationSchurMultiplicity_mul_end_le_of_section_uniform_targetHom
    {k G V W X : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    (rho : Representation k G V) (tau : Representation k G W)
    (sigma : Representation k G X)
    [IsSimpleModule k[G] sigma.asModule]
    (cap : ℕ)
    (hHom : ∀ N : Subrepresentation rho,
      Module.finrank k (N.toRepresentation.IntertwiningMap sigma) ≤ cap)
    (M : Subrepresentation rho)
    (q : M.toRepresentation.IntertwiningMap tau) (hq : Function.Surjective q) :
    schurSocleMultiplicity (k := k) (R := k[G])
        (A := tau.asModule) (X := sigma.asModule) *
      Module.finrank k (Module.End k[G] sigma.asModule) ≤ cap := by
  have hmodule : ∀ N : Submodule k[G] rho.asModule,
      Module.finrank k (N →ₗ[k[G]] sigma.asModule) ≤ cap := by
    intro N
    have h := hHom (Subrepresentation.ofSubmodule' N)
    rw [(Representation.IntertwiningMap.equivLinearMapAsModule _ sigma).finrank_eq] at h
    rw [(schurHomCongrSource (k := k) (A := sigma.asModule)
      (submoduleRepresentationModuleEquiv rho N)).finrank_eq]
    exact h
  let e := submoduleRepresentationModuleEquiv rho M.asSubmodule
  let f : M.toRepresentation.asModule →ₗ[k[G]] tau.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule M.toRepresentation tau q
  let q' : M.asSubmodule →ₗ[k[G]] tau.asModule := f.comp e.toLinearMap
  have hq' : Function.Surjective q' := hq.comp e.surjective
  exact schurSocleMultiplicity_mul_end_le_of_section_uniform_targetHom
    (k := k) (R := k[G]) (X := sigma.asModule)
    cap hmodule M.asSubmodule q' hq'

end SymmetricSubgroupAsymptotics

end
