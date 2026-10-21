import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! A reversible coordinate change retains the exact original invariant
subspace and its intrinsic coinvariants. No semisimplicity is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G V Z : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup Z] [Module k Z]

/-- Coinvariants respect a proved equivalence of representations. -/
def representationEquivCoinvariants
    {rho : Representation k G V} {sigma : Representation k G Z}
    (e : rho.Equiv sigma) : rho.Coinvariants ≃ₗ[k] sigma.Coinvariants where
  toLinearMap := Representation.Coinvariants.map rho sigma e.toIntertwiningMap
  invFun := Representation.Coinvariants.map sigma rho e.symm.toIntertwiningMap
  left_inv v := by
    induction v using Representation.Coinvariants.induction_on with
    | h v =>
      change Representation.Coinvariants.mk rho (e.toLinearEquiv.symm (e.toLinearEquiv v)) = _
      rw [e.toLinearEquiv.symm_apply_apply]
  right_inv z := by
    induction z using Representation.Coinvariants.induction_on with
    | h z =>
      change Representation.Coinvariants.mk sigma (e.toLinearEquiv (e.toLinearEquiv.symm z)) = _
      rw [e.toLinearEquiv.apply_symm_apply]

namespace RepresentationCoordinateChange

variable (rho : Representation k G V) (e : V ≃ₗ[k] Z)

/-- The same action expressed in the new reversible coordinates. -/
def action : Representation k G Z := (e.conjAlgEquiv k).toMonoidHom.comp rho

@[simp] theorem action_apply (g : G) (z : Z) :
    action rho e g z = e (rho g (e.symm z)) := rfl

/-- The image of the original invariant subspace, with its correlated
vectors retained by an injective coordinate change. -/
def subrepresentation (B : Subrepresentation rho) : Subrepresentation (action rho e) where
  toSubmodule := B.toSubmodule.map e.toLinearMap
  apply_mem_toSubmodule g z hz := by
    obtain ⟨v,hv,rfl⟩ := hz
    refine ⟨rho g v,B.apply_mem_toSubmodule g hv,?_⟩
    change e (rho g v) = e (rho g (e.symm (e v)))
    rw [e.symm_apply_apply]

/-- The original subrepresentation and its coordinate image are
intertwining-equivalent, not merely equidimensional. -/
def subrepresentationEquiv (B : Subrepresentation rho) :
    B.toRepresentation.Equiv (subrepresentation rho e B).toRepresentation :=
  .mk (e.submoduleMap B.toSubmodule) (by
    intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change e (rho g v.val) = e (rho g (e.symm (e v.val)))
    rw [e.symm_apply_apply])

/-- The numerical head is the head of the same original subspace. -/
theorem subrepresentation_head (B : Subrepresentation rho) :
    Module.finrank k B.toRepresentation.Coinvariants =
      Module.finrank k (subrepresentation rho e B).toRepresentation.Coinvariants :=
  (representationEquivCoinvariants (subrepresentationEquiv rho e B)).finrank_eq

/-- Membership remains an exact reversible statement on original vectors. -/
theorem mem_subrepresentation_iff (B : Subrepresentation rho) (z : Z) :
    z ∈ (subrepresentation rho e B).toSubmodule ↔ e.symm z ∈ B.toSubmodule := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    change e.symm (e v) ∈ B.toSubmodule
    rwa [e.symm_apply_apply]
  · intro hz
    exact ⟨e.symm z,hz,e.apply_symm_apply z⟩

end RepresentationCoordinateChange
end SymmetricSubgroupAsymptotics
