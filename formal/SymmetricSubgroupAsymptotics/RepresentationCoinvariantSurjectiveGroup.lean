import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Restricting an action along an onto group map preserves its exact
coinvariant denominator. No averaging or semisimplicity is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k A T V : Type*} [Field k] [Group A] [Group T]
  [AddCommGroup V] [Module k V]

theorem coinvariants_ker_comp_surjective_group
    (rho : Representation k T V) (f : A →* T) (hf : Function.Surjective f) :
    Representation.Coinvariants.ker (rho.comp f) = Representation.Coinvariants.ker rho := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker (f a) v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨t, v⟩, rfl⟩
    obtain ⟨a, rfl⟩ := hf t
    exact Representation.Coinvariants.sub_mem_ker (ρ := rho.comp f) a v

theorem coinvariants_finrank_comp_surjective_group
    (rho : Representation k T V) (f : A →* T) (hf : Function.Surjective f) :
    Module.finrank k (Representation.Coinvariants (rho.comp f)) = Module.finrank k rho.Coinvariants :=
  (Submodule.quotEquivOfEq _ _ (coinvariants_ker_comp_surjective_group rho f hf)).finrank_eq

end SymmetricSubgroupAsymptotics
