import SymmetricSubgroupAsymptotics.RepresentationAlgebraPolynomialGeneratorBound
import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators

/-! Transport uniform generator bounds between represented modules and
their actual group-algebra submodules. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

namespace ModuleGeneratedBy

variable {R M N : Type} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem uniform_congr (e : M ≃ₗ[R] N) {n : ℕ}
    (h : ∀ W : Submodule R M, ModuleGeneratedBy R W n)
    (W : Submodule R N) : ModuleGeneratedBy R W n := by
  let f : W.comap e.toLinearMap ≃ₗ[R] W :=
    { toFun := fun x ↦ ⟨e x, x.2⟩
      invFun := fun y ↦ ⟨e.symm y, by
        change e (e.symm (y : N)) ∈ W
        rw [e.apply_symm_apply]
        exact y.property⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y)
      map_add' := fun _ _ ↦ Subtype.ext (e.map_add _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (e.map_smul _ _) }
  exact congr f (h _)

end ModuleGeneratedBy

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {rho : Representation k G V}

/-- The represented subspace and the corresponding group-algebra
submodule have the same actual scalar action. -/
def subrepresentationModuleEquiv (W : Subrepresentation rho) :
    W.toRepresentation.asModule ≃ₗ[k[G]] W.asSubmodule where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    change (W.toRepresentation.asAlgebraHom a x : V) = rho.asAlgebraHom a x.1
    rw [subrepresentation_asAlgebraHom_restrict]
    rfl

theorem uniformSubrepresentationGeneratorBound_iff_submodule
    (rho : Representation k G V) (n : ℕ) :
    UniformSubrepresentationGeneratorBound rho n ↔
      ∀ W : Submodule k[G] rho.asModule, ModuleGeneratedBy k[G] W n := by
  constructor
  · intro h W
    let S := Subrepresentation.ofSubmodule' W
    exact ModuleGeneratedBy.congr (subrepresentationModuleEquiv S) (h S)
  · intro h W
    exact ModuleGeneratedBy.congr (subrepresentationModuleEquiv W).symm
      (h W.asSubmodule)

end SymmetricSubgroupAsymptotics

end
