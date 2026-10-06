import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead
import SymmetricSubgroupAsymptotics.RepresentationSchurRows
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Semisimple

/-!
# Vanishing coinvariants exclude fixed simple rows

A fixed simple submodule of a semisimple representation is a quotient of the
whole representation: project along an invariant complement.  The projection
is constant on the group action, so it descends to the literal coinvariants.
Consequently zero-dimensional coinvariants exclude every fixed simple row.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- A fixed submodule of a semisimple representation is a quotient of its
literal coinvariants. -/
theorem coinvariants_surject_fixed_submodule
    (sigma : Representation k G V)
    [IsSemisimpleModule k[G] sigma.asModule]
    (S : Submodule k[G] sigma.asModule)
    (hfixed : representationSubmoduleFixed sigma S) :
    ∃ f : sigma.Coinvariants →ₗ[k] S, Function.Surjective f := by
  obtain ⟨J, hSJ⟩ := exists_isCompl S
  let projR : sigma.asModule →ₗ[k[G]] S :=
    S.projectionOnto J hSJ
  let proj : V →ₗ[k] S := projR.restrictScalars k
  have haction (g : G) : proj.comp (sigma g) = proj := by
    apply LinearMap.ext
    intro v
    change projR (sigma.asModuleEquiv.symm (sigma g v)) =
      projR (sigma.asModuleEquiv.symm v)
    have hmodule : sigma.asModuleEquiv.symm (sigma g v) =
        MonoidAlgebra.single g (1 : k) • sigma.asModuleEquiv.symm v := by
      apply sigma.asModuleEquiv.injective
      rw [Representation.asModuleEquiv_map_smul,
        Representation.asAlgebraHom_single, one_smul,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [hmodule, projR.map_smul]
    exact hfixed g (projR v)
  let f : sigma.Coinvariants →ₗ[k] S :=
    Representation.Coinvariants.lift sigma proj haction
  refine ⟨f, ?_⟩
  intro s
  refine ⟨Representation.Coinvariants.mk sigma (sigma.asModuleEquiv s.1), ?_⟩
  change projR (s : sigma.asModule) = s
  exact Submodule.projectionOnto_apply_left hSJ s

/-- In a finite-dimensional semisimple representation, vanishing literal
coinvariants exclude every fixed simple submodule. -/
theorem not_representationSubmoduleFixed_of_semisimple_coinvariants_zero
    (sigma : Representation k G V)
    [FiniteDimensional k V]
    [IsSemisimpleModule k[G] sigma.asModule]
    (hzero : Module.finrank k sigma.Coinvariants = 0)
    (S : Submodule k[G] sigma.asModule)
    [IsSimpleModule k[G] S] :
    ¬ representationSubmoduleFixed sigma S := by
  intro hfixed
  obtain ⟨f, hf⟩ := coinvariants_surject_fixed_submodule sigma S hfixed
  letI : FiniteDimensional k S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective
  have hdim : Module.finrank k S ≤ Module.finrank k sigma.Coinvariants :=
    LinearMap.finrank_le_finrank_of_surjective hf
  rw [hzero] at hdim
  have hSzero : Module.finrank k S = 0 := Nat.eq_zero_of_le_zero hdim
  letI : Nontrivial S := IsSimpleModule.nontrivial k[G] S
  exact (Module.finrank_pos (R := k) (M := S)).ne' hSzero

end SymmetricSubgroupAsymptotics

end
