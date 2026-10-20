import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection

/-! Maschke embedding for an actual equivariant quotient. The retained
surjection is the only quotient input; no invariant-state census or
quotient generator premise is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

variable {k G V W : Type} [Field k] [Group G] [Finite G]
  [NeZero (Nat.card G : k)]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Every actual equivariant quotient of a representation of invertible
finite-group order embeds equivariantly into the original representation. -/
theorem original_equivariant_quotient_embedding
    (rho : Representation k G V) (sigma : Representation k G W)
    (f : rho.IntertwiningMap sigma) (hf : Function.Surjective f) :
    ∃ i : sigma.IntertwiningMap rho, Function.Injective i := by
  let F : rho.asModule →ₗ[k[G]] sigma.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rho sigma f
  have hF : Function.Surjective F := hf
  obtain ⟨C,hC⟩ := MonoidAlgebra.Submodule.exists_isCompl (LinearMap.ker F)
  let e : sigma.asModule ≃ₗ[k[G]] C :=
    (F.quotKerEquivOfSurjective hF).symm.trans
      ((LinearMap.ker F).quotientEquivOfIsCompl C hC)
  let I : sigma.asModule →ₗ[k[G]] rho.asModule := C.subtype.comp e.toLinearMap
  let i : sigma.IntertwiningMap rho :=
    (Representation.IntertwiningMap.equivLinearMapAsModule sigma rho).symm I
  refine ⟨i,?_⟩
  have hI : Function.Injective I := Subtype.val_injective.comp e.injective
  exact hI

end SymmetricSubgroupAsymptotics
end
