import SymmetricSubgroupAsymptotics.InducedTernaryWidthGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import Mathlib.RepresentationTheory.Maschke

/-!
# Cyclic subrepresentations from a coprime cyclic restriction

Suppose a representation becomes cyclic after restriction to a finite
subgroup whose order is invertible in the coefficient field.  Maschke's
theorem supplies an equivariant projection from the restricted ambient
module onto each restricted subrepresentation.  Projecting one ambient
generator therefore gives one generator of that subrepresentation.  The
same vector also generates for the original group.

This is the reusable algebraic step in the signed-isotype argument.  The
subgroup will be a transitive binary subgroup of one coordinate isotype,
over `F3`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u

variable {k G V : Type u} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- If the restriction of an ambient representation to a finite coprime
subgroup is cyclic, then every subrepresentation of the ambient
representation is cyclic. -/
theorem uniformSubrepresentationGeneratorBound_of_coprime_cyclic_restriction
    (rho : Representation k G V)
    (P : Subgroup G) [Finite P] [NeZero (Nat.card P : k)]
    (hcyclic : RepresentationGeneratedBy (rho.comp P.subtype) 1) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  intro M
  let rhoP : Representation k P V := rho.comp P.subtype
  let MP : Subrepresentation rhoP :=
    { toSubmodule := M.toSubmodule
      apply_mem_toSubmodule := fun g x hx => M.apply_mem_toSubmodule g.1 hx }
  let inclusion : MP.toRepresentation.IntertwiningMap rhoP :=
    { toLinearMap := MP.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let inclusionModule : MP.toRepresentation.asModule →ₗ[k[P]] rhoP.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule
      MP.toRepresentation rhoP inclusion
  let identityModule : MP.toRepresentation.asModule →ₗ[k[P]]
      MP.toRepresentation.asModule := LinearMap.id
  obtain ⟨projectionModule, hprojection⟩ :=
    IsSemisimpleModule.extension_property inclusionModule
      MP.toSubmodule.injective_subtype identityModule
  let projection : rhoP.IntertwiningMap MP.toRepresentation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      rhoP MP.toRepresentation).symm projectionModule
  have hprojection_surjective : Function.Surjective projection := by
    intro x
    refine ⟨x.1, ?_⟩
    have hx := LinearMap.congr_fun hprojection x
    exact hx
  have hrestricted : RepresentationGeneratedBy MP.toRepresentation 1 :=
    representationGeneratedBy_of_surjective rhoP MP.toRepresentation
      projection hprojection_surjective hcyclic
  apply representationGeneratedBy_of_subgroup_restriction P M.toRepresentation
  simpa only [MP, Subrepresentation.toRepresentation] using hrestricted

end SymmetricSubgroupAsymptotics

end
