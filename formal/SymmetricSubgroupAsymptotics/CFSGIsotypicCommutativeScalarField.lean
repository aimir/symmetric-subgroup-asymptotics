import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RepresentationTheory.Irreducible

/-! A nonzero finite semisimple isotypic module over a commutative ring
has maximal annihilator. For an actual abelian-group representation this
identifies its scalar-image quotient as a genuine field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGIsotypicCommutativeScalarField

theorem annihilator_isMaximal_of_isotypic
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] [IsSemisimpleModule R M]
    (h : IsIsotypic R M) : (Module.annihilator R M).IsMaximal := by
  obtain ⟨n, hn, S, hs, ⟨e⟩⟩ := h.linearEquiv_fun
  letI : NeZero n := hn
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  letI : IsSimpleModule R S := hs
  have he : Module.annihilator R M = Module.annihilator R S := by
    rw [e.annihilator_eq, Module.annihilator_pi]
    simp
  rw [he]
  exact IsSimpleModule.annihilator_isMaximal

variable {k A V : Type} [Field k] [CommGroup A]
  [AddCommGroup V] [Module k V] (rho : Representation k A V)

local instance scalarFieldRepresentationModule : Module k[A] rho.asModule :=
  Representation.instModuleMonoidAlgebraAsModule rho

theorem scalar_kernel_eq_annihilator :
    RingHom.ker rho.asAlgebraHom.toRingHom = Module.annihilator k[A] rho.asModule := by
  apply Ideal.ext
  intro r
  rw [RingHom.mem_ker, Module.mem_annihilator]
  constructor
  · intro hr v
    change rho.asAlgebraHom r = 0 at hr
    apply rho.asModuleEquiv.injective
    simp only [rho.asModuleEquiv_map_smul, hr, LinearMap.zero_apply, map_zero]
  · intro hr
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := rho.asModuleEquiv.surjective v
    change rho.asAlgebraHom r (rho.asModuleEquiv w) = 0
    rw [← rho.asModuleEquiv_map_smul, hr, map_zero]

theorem scalar_kernel_isMaximal :
    letI : Module k[A] rho.asModule := Representation.instModuleMonoidAlgebraAsModule rho
    ∀ [Module.Finite k[A] rho.asModule] [Nontrivial rho.asModule]
      [IsSemisimpleModule k[A] rho.asModule],
      IsIsotypic k[A] rho.asModule → (RingHom.ker rho.asAlgebraHom.toRingHom).IsMaximal := by
  letI : Module k[A] rho.asModule := Representation.instModuleMonoidAlgebraAsModule rho
  intro _ _ _ h
  rw [scalar_kernel_eq_annihilator]
  exact annihilator_isMaximal_of_isotypic k[A] rho.asModule h

/-- The actual group-algebra quotient acting on the given module. -/
abbrev scalarQuotient := k[A] ⧸ RingHom.ker rho.asAlgebraHom.toRingHom

@[reducible] noncomputable def scalarField :
    letI : Module k[A] rho.asModule := Representation.instModuleMonoidAlgebraAsModule rho
    ∀ [Module.Finite k[A] rho.asModule] [Nontrivial rho.asModule]
      [IsSemisimpleModule k[A] rho.asModule],
      IsIsotypic k[A] rho.asModule → Field (scalarQuotient rho) := by
  letI : Module k[A] rho.asModule := Representation.instModuleMonoidAlgebraAsModule rho
  intro _ _ _ h
  letI : (RingHom.ker rho.asAlgebraHom.toRingHom).IsMaximal := scalar_kernel_isMaximal rho h
  exact Ideal.Quotient.field (RingHom.ker rho.asAlgebraHom.toRingHom)

end SymmetricSubgroupAsymptotics.CFSGIsotypicCommutativeScalarField
