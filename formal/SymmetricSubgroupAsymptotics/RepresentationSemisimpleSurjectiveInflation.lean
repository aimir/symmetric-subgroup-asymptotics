import SymmetricSubgroupAsymptotics.RepresentationSimpleTargetSurjectiveDescent
import Mathlib.RepresentationTheory.Semisimple

/-! Actual surjective inflation preserves the whole semisimple target. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

theorem representation_isSemisimpleModule_comp
    {k G H V : Type} [Field k] [Group G] [Group H]
    [AddCommGroup V] [Module k V]
    (gamma : G →* H) (hgamma : Function.Surjective gamma)
    (sigma : Representation k H V) [IsSemisimpleModule k[H] sigma.asModule] :
    IsSemisimpleModule k[G] (Representation.asModule (sigma.comp gamma)) := by
  let phi := MonoidAlgebra.mapDomainRingHom k gamma
  letI : RingHomSurjective phi := ⟨Finsupp.mapDomain_surjective hgamma⟩
  let f : Representation.asModule (sigma.comp gamma) →ₛₗ[phi] sigma.asModule := {
    toFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun r x => representation_comp_monoidAlgebra_smul gamma sigma r x }
  exact (f.isSemisimpleModule_iff_of_bijective
    ⟨Function.injective_id, Function.surjective_id⟩).mpr inferInstance

end SymmetricSubgroupAsymptotics

end
