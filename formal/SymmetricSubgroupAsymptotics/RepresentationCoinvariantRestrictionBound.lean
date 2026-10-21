import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Restricting the acting group removes coinvariant relations. This is
a bound for the same vector space, not a claim that submodule heads are
monotone under ambient vector-space inclusions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G H V : Type} [Field k] [Group G] [Group H]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem coinvariants_finrank_le_comp_group
    (rho : Representation k G V) (f : H →* G) :
    Module.finrank k rho.Coinvariants ≤
      Module.finrank k (Representation.Coinvariants (rho.comp f)) := by
  let q : Representation.Coinvariants (rho.comp f) →ₗ[k] rho.Coinvariants :=
    Representation.Coinvariants.lift (rho.comp f)
      (Representation.Coinvariants.mk rho) (by
        intro h
        apply LinearMap.ext
        intro v
        exact Representation.Coinvariants.mk_self_apply rho (f h) v)
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨v, hv⟩ := Representation.Coinvariants.mk_surjective rho a
    exact ⟨Representation.Coinvariants.mk (rho.comp f) v, hv⟩
  exact LinearMap.finrank_le_finrank_of_surjective hq

end SymmetricSubgroupAsymptotics
