import SymmetricSubgroupAsymptotics.RepresentationGeneratorExtension
import Mathlib.RepresentationTheory.Maschke

/-!
# Generator bounds from a restricted semisimple action

Generation by a tuple persists when the acting group is enlarged. For a
finite group of invertible order, Maschke's retraction turns any generating
tuple of the ambient representation into a generating tuple of every
subrepresentation. Neither statement requires an invariant-state census.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {k G L V : Type} [Field k] [Group G] [Group L]
  [AddCommGroup V] [Module k V]

namespace RepresentationGeneratedBy

/-- Enlarging the acting image preserves a module-generating tuple. The
homomorphism need not be injective or surjective. -/
theorem of_comp (rho : Representation k G V) (f : L →* G)
    {n : ℕ} (hgen : RepresentationGeneratedBy (rho.comp f) n) :
    RepresentationGeneratedBy rho n := by
  let rhoL : Representation k L V := rho.comp f
  obtain ⟨v, hv⟩ := hgen
  let w : Fin n → rho.asModule := fun j ↦
    rho.asModuleEquiv.symm (rhoL.asModuleEquiv (v j))
  let P : Submodule k[G] rho.asModule := Submodule.span k[G] (Set.range w)
  let MG : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  let ML : Subrepresentation rhoL :=
    { toSubmodule := MG.toSubmodule
      apply_mem_toSubmodule := fun g _ hx ↦ MG.apply_mem_toSubmodule (f g) hx }
  have hle : Submodule.span k[L] (Set.range v) ≤ ML.asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change w j ∈ P
    exact Submodule.subset_span ⟨j, rfl⟩
  have hML : ML.asSubmodule = ⊤ := by
    rw [hv] at hle
    exact top_unique hle
  refine ⟨w, top_unique ?_⟩
  intro x _
  have hx : rhoL.asModuleEquiv.symm (rho.asModuleEquiv x) ∈ ML.asSubmodule := by
    rw [hML]
    exact Submodule.mem_top
  exact hx

/-- Maschke's equivariant retraction makes the ambient generator bound
uniform over all subrepresentations. -/
theorem uniform_of_invertible_order [Finite G] [NeZero (Nat.card G : k)]
    (rho : Representation k G V) {n : ℕ}
    (hgen : RepresentationGeneratedBy rho n) :
    UniformSubrepresentationGeneratorBound rho n := by
  intro W
  let inclusion : W.toRepresentation.IntertwiningMap rho :=
    { toLinearMap := W.toSubmodule.subtype
      isIntertwining' _ := rfl }
  let I : W.toRepresentation.asModule →ₗ[k[G]] rho.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ inclusion
  have hI : Function.Injective I := fun _ _ h ↦ Subtype.ext h
  obtain ⟨P, hP⟩ := MonoidAlgebra.exists_leftInverse_of_injective I
    (LinearMap.ker_eq_bot.mpr hI)
  let projection : rho.IntertwiningMap W.toRepresentation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm P
  have hsurj : Function.Surjective projection := by
    intro y
    refine ⟨inclusion y, ?_⟩
    exact LinearMap.congr_fun hP y
  exact representationGeneratedBy_of_surjective rho W.toRepresentation
    projection hsurj hgen

end RepresentationGeneratedBy

namespace UniformSubrepresentationGeneratorBound

/-- A uniform bound for any restricted acting image also bounds the
original representation, without a finite invariant registry. -/
theorem of_comp (rho : Representation k G V) (f : L →* G)
    {n : ℕ} (hgen : UniformSubrepresentationGeneratorBound (rho.comp f) n) :
    UniformSubrepresentationGeneratorBound rho n := by
  intro W
  let restricted : Subrepresentation (rho.comp f) :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := fun g _ hx ↦ W.apply_mem_toSubmodule (f g) hx }
  exact RepresentationGeneratedBy.of_comp W.toRepresentation f (hgen restricted)

end UniformSubrepresentationGeneratorBound
end SymmetricSubgroupAsymptotics

end
