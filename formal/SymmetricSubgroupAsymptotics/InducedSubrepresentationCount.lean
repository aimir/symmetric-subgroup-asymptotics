import SymmetricSubgroupAsymptotics.TraceyPrimePowerInput
import Mathlib.FieldTheory.Finiteness

/-!
# Counting invariant subspaces from uniform module generators

The affine chief-layer argument must count an invariant kernel and its
extension fibre together.  The invariant-kernel part is elementary once a
uniform module-generator theorem is available: choose a padded generating
tuple in every invariant subspace.  Equality of the ambient tuples forces
equality of their group-algebra spans, hence equality of the subspaces.

This file contains that deduction only.  The generator theorem used by the
affine application is Tracey's published induced-module theorem and is kept
as a separately named literature input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u

variable {k G V : Type u} [Field k] [Finite k] [Group G]
  [AddCommGroup V] [Module k V] [Finite V]

/-- Every invariant subspace of one representation has a generating tuple
of the same padded length. -/
def UniformSubrepresentationGeneratorBound
    (rho : Representation k G V) (H : ℕ) : Prop :=
  ∀ M : Subrepresentation rho,
    RepresentationGeneratedBy M.toRepresentation H

namespace UniformSubrepresentationGeneratorBound

variable {rho : Representation k G V} {H : ℕ}
  (hgen : UniformSubrepresentationGeneratorBound rho H)

private noncomputable def chosenGenerators
    (M : Subrepresentation rho) : Fin H → M.toRepresentation.asModule :=
  Classical.choose (hgen M)

private theorem chosenGenerators_span
    (M : Subrepresentation rho) :
    letI : Module k[G] M.toRepresentation.asModule :=
      M.toRepresentation.instModuleMonoidAlgebraAsModule
    Submodule.span k[G] (Set.range (chosenGenerators hgen M)) = ⊤ := by
  exact Classical.choose_spec (hgen M)

/-- The padded tuple, viewed in the original ambient vector space. -/
private noncomputable def code
    (M : Subrepresentation rho) : Fin H → rho.asModule :=
  fun i => rho.asModuleEquiv.symm (chosenGenerators hgen M i).1

private theorem asSubmodule_eq_span_code
    (M : Subrepresentation rho) :
    M.asSubmodule = Submodule.span k[G] (Set.range (code hgen M)) := by
  letI : Module k[G] M.toRepresentation.asModule :=
    M.toRepresentation.instModuleMonoidAlgebraAsModule
  let inclusion : M.toRepresentation.IntertwiningMap rho :=
    { toLinearMap := M.toSubmodule.subtype
      isIntertwining' _ := rfl }
  let f : M.toRepresentation.asModule →ₗ[k[G]] rho.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule
      M.toRepresentation rho inclusion
  have hmap := congrArg (Submodule.map f) (chosenGenerators_span hgen M)
  rw [Submodule.map_top, Submodule.map_span] at hmap
  rw [← Set.range_comp] at hmap
  have hrange : LinearMap.range f = M.asSubmodule := by
    apply SetLike.ext
    intro v
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hv
      refine ⟨⟨rho.asModuleEquiv v, hv⟩, ?_⟩
      exact rho.asModuleEquiv.symm_apply_apply v
  rw [hrange] at hmap
  simpa only [f, code, Function.comp_def] using hmap.symm

private theorem code_injective : Function.Injective (code hgen) := by
  intro M N hMN
  apply Subrepresentation.toSubmodule_injective
  have hspan : Submodule.span k[G] (Set.range (code hgen M)) =
      Submodule.span k[G] (Set.range (code hgen N)) := by rw [hMN]
  have hgroup : M.asSubmodule = N.asSubmodule := by
    rw [asSubmodule_eq_span_code hgen M,
      asSubmodule_eq_span_code hgen N, hspan]
  apply SetLike.ext
  intro x
  change x ∈ M.asSubmodule ↔ x ∈ N.asSubmodule
  rw [hgroup]

include hgen
/-- A uniform `H`-generator theorem gives the literal invariant-subspace
count `|Subrep rho| ≤ |V|^H`.  No semisimplicity is used. -/
theorem card_subrepresentation_le :
    Nat.card (Subrepresentation rho) ≤ Nat.card V ^ H := by
  letI : Finite rho.asModule :=
    Finite.of_equiv V rho.asModuleEquiv.symm.toEquiv
  calc
    Nat.card (Subrepresentation rho) ≤ Nat.card (Fin H → rho.asModule) :=
      Nat.card_le_card_of_injective (code hgen) (code_injective hgen)
    _ = Nat.card V ^ H := by
      rw [Nat.card_fun, Nat.card_fin,
        Nat.card_congr rho.asModuleEquiv.toEquiv]

end UniformSubrepresentationGeneratorBound
end SymmetricSubgroupAsymptotics

end
