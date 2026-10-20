import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import Mathlib.RingTheory.SimpleModule.Basic

/-! A generator bound on a semisimple represented module is uniform over
all its invariant subspaces. Semisimplicity belongs to the actual module;
the acting group may have order divisible by the characteristic. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace RepresentationGeneratedBy

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

theorem uniform_of_semisimple (rho : Representation k G V)
    [IsSemisimpleModule k[G] rho.asModule] {n : ℕ}
    (hgen : RepresentationGeneratedBy rho n) :
    UniformSubrepresentationGeneratorBound rho n := by
  intro W
  let inclusion : W.toRepresentation.IntertwiningMap rho :=
    { toLinearMap := W.toSubmodule.subtype
      isIntertwining' _ := rfl }
  let I : W.toRepresentation.asModule →ₗ[k[G]] rho.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ inclusion
  have hI : Function.Injective I := fun _ _ h ↦ Subtype.ext h
  obtain ⟨P, hP⟩ := IsSemisimpleModule.extension_property I hI LinearMap.id
  let projection : rho.IntertwiningMap W.toRepresentation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm P
  have hsurj : Function.Surjective projection := by
    intro y
    refine ⟨inclusion y, ?_⟩
    exact LinearMap.congr_fun hP y
  exact representationGeneratedBy_of_surjective rho W.toRepresentation
    projection hsurj hgen

end RepresentationGeneratedBy
end SymmetricSubgroupAsymptotics

end
