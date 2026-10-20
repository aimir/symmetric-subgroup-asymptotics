import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput

/-! A scalar basis is also a group-algebra generating tuple.
This elementary bound is used only on the proper submodules of the
three-dimensional Jordan-plus-trivial part of the S3 envelope. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

theorem representationGeneratedBy_scalar_finrank
    {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (rho : Representation k G V) :
    RepresentationGeneratedBy rho (Module.finrank k V) := by
  let b := Module.finBasis k V
  let v : Fin (Module.finrank k V) → rho.asModule :=
    fun i => rho.asModuleEquiv.symm (b i)
  let P : Submodule k[G] rho.asModule := Submodule.span _ (Set.range v)
  let S : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  have hle : Submodule.span k (Set.range b) ≤ S.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change v i ∈ P
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨v, top_unique ?_⟩
  intro x _
  change rho.asModuleEquiv x ∈ S
  apply hle
  rw [b.span_eq]
  trivial

theorem representationGeneratedBy_of_scalar_finrank_le
    {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (rho : Representation k G V) {n : ℕ}
    (h : Module.finrank k V ≤ n) : RepresentationGeneratedBy rho n :=
  representationGeneratedBy_mono rho h (representationGeneratedBy_scalar_finrank rho)

end SymmetricSubgroupAsymptotics

end
