import SymmetricSubgroupAsymptotics.SurjectiveCoinducedDescent
import SymmetricSubgroupAsymptotics.SchurRepresentation

/-!
# Retaining a simple target across an original surjective action

The source is an actual subrepresentation of the inflated original
module. Descending it changes neither its vectors nor its linear maps.
The same holds for a simple target killed by the displayed kernel. Thus
a uniform target-Hom bound over the literal top transfers to the original
group without selecting a different simple type or a finite state.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {k G H V W : Type} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Surjective inflation also reflects simplicity. -/
theorem representation_isSimpleModule_of_comp
    (gamma : G →* H) (hgamma : Function.Surjective gamma)
    (sigma : Representation k H W)
    [IsSimpleModule k[G] (inflatedRepresentation gamma sigma).asModule] :
    IsSimpleModule k[H] sigma.asModule := by
  let phi := MonoidAlgebra.mapDomainRingHom k gamma
  letI : RingHomSurjective phi := ⟨Finsupp.mapDomain_surjective hgamma⟩
  let f : (inflatedRepresentation gamma sigma).asModule →ₛₗ[phi] sigma.asModule :=
    { toFun := fun x ↦ x
      map_add' := by intro x y; rfl
      map_smul' := by
        intro r x
        exact representation_comp_monoidAlgebra_smul gamma sigma r x }
  exact (f.isSimpleModule_iff_of_bijective
    ⟨Function.injective_id, Function.surjective_id⟩).mp inferInstance

/-- Descent followed by the original surjection is the original action. -/
theorem representationDescend_comp_eq
    (gamma : G →* H) (hgamma : Function.Surjective gamma)
    (sigma : Representation k G W) (hker : gamma.ker ≤ sigma.ker) :
    inflatedRepresentation gamma (representationDescend gamma hgamma sigma hker) =
      sigma := by
  apply MonoidHom.ext
  intro g
  exact representationDescend_apply gamma hgamma sigma hker g

/-- The displayed subrepresentation descends on exactly the same scalar
submodule. Surjectivity supplies stability under every literal top element. -/
def subrepresentationDescendOfComp
    (gamma : G →* H) (hgamma : Function.Surjective gamma)
    (rho : Representation k H V)
    (M : Subrepresentation (inflatedRepresentation gamma rho)) :
    Subrepresentation rho where
  toSubmodule := M.toSubmodule
  apply_mem_toSubmodule := by
    intro h v hv
    obtain ⟨g, rfl⟩ := hgamma h
    exact M.apply_mem_toSubmodule g hv

/-- A uniform bound on maps to simple literal targets transfers through
the exact original surjection, retaining both target dimensions. -/
theorem uniform_simple_targetHom_le_of_surjective
    [FiniteDimensional k V] [FiniteDimensional k W]
    (gamma : G →* H) (hgamma : Function.Surjective gamma)
    (rho : Representation k H V)
    (sigma : Representation k G W)
    [IsSimpleModule k[G] sigma.asModule]
    (hker : gamma.ker ≤ sigma.ker)
    (d e cap : ℕ)
    (hdim : Module.finrank k W = d)
    (hEnd : Module.finrank k (Module.End k[G] sigma.asModule) = e)
    (hbound : ∀ tau : Representation k H W,
      [IsSimpleModule k[H] tau.asModule] →
      Module.finrank k W = d →
      Module.finrank k (Module.End k[H] tau.asModule) = e →
      ∀ N : Subrepresentation rho,
        Module.finrank k (N.toRepresentation.IntertwiningMap tau) ≤ cap)
    (M : Subrepresentation (inflatedRepresentation gamma rho)) :
    Module.finrank k (M.toRepresentation.IntertwiningMap sigma) ≤ cap := by
  let tau := representationDescend gamma hgamma sigma hker
  have htau : inflatedRepresentation gamma tau = sigma :=
    representationDescend_comp_eq gamma hgamma sigma hker
  letI : IsSimpleModule k[G] (inflatedRepresentation gamma tau).asModule := by
    rw [htau]
    infer_instance
  letI : IsSimpleModule k[H] tau.asModule :=
    representation_isSimpleModule_of_comp gamma hgamma tau
  have hEnd' : Module.finrank k (Module.End k[H] tau.asModule) = e := by
    rw [← representationEnd_finrank_comp_eq gamma hgamma tau, htau]
    exact hEnd
  let N := subrepresentationDescendOfComp gamma hgamma rho M
  have h := hbound tau hdim hEnd' N
  have he := (representationIntertwiningCompEquiv gamma hgamma
    N.toRepresentation tau).finrank_eq
  rw [htau] at he
  change Module.finrank k (N.toRepresentation.IntertwiningMap tau) =
    Module.finrank k (M.toRepresentation.IntertwiningMap sigma) at he
  exact he ▸ h

end SymmetricSubgroupAsymptotics

end
