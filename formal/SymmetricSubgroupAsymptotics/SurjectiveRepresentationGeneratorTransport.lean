import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.InducedTernaryWidthGenerators
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Generator bounds under a surjective change of acting group

Pulling a representation back along a surjective group homomorphism does
not change the available orbit operators: every target-group element has a
source-group lift.  Thus a generating tuple, and uniformly every cyclic
subrepresentation, pulls back with the same length.

This is the group-coordinate transport needed to compare a literal
three-point signed Sylow image with the standard `C3` permutation module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Pointwise

namespace SymmetricSubgroupAsymptotics

universe u

variable {k G H V : Type u} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V]

/-- A generating tuple remains generating after a representation is pulled
back along a surjective homomorphism of acting groups. -/
theorem representationGeneratedBy_comp_of_surjective
    (sigma : Representation k H V) (phi : G →* H)
    (hphi : Function.Surjective phi) {n : ℕ}
    (hgen : RepresentationGeneratedBy sigma n) :
    RepresentationGeneratedBy (sigma.comp phi) n := by
  let rho : Representation k G V := sigma.comp phi
  letI : Module k[G] rho.asModule :=
    Representation.instModuleMonoidAlgebraAsModule rho
  obtain ⟨v, hv⟩ := hgen
  let vG : Fin n → rho.asModule := fun i ↦
    rho.asModuleEquiv.symm (sigma.asModuleEquiv (v i))
  let W : Submodule k[G] rho.asModule :=
    Submodule.span k[G] (Set.range vG)
  have haction : ∀ (r : k[G]) (a : V),
      rho.asModuleEquiv (r • rho.asModuleEquiv.symm a) =
        sigma.asModuleEquiv
          ((MonoidAlgebra.mapDomainRingHom k phi r) •
            sigma.asModuleEquiv.symm a) := by
    intro r a
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
        rw [map_add, add_smul, add_smul, map_add, hx, hy]
        exact (map_add sigma.asModuleEquiv _ _).symm
    | single g t =>
        simp only [MonoidAlgebra.mapDomainRingHom_apply,
          MonoidAlgebra.mapDomain_single, Representation.single_smul,
          map_smul, LinearEquiv.apply_symm_apply, rho]
        rfl
  refine ⟨vG, top_unique ?_⟩
  intro x _hx
  let xH : sigma.asModule :=
    sigma.asModuleEquiv.symm (rho.asModuleEquiv x)
  have hxH : xH ∈ Submodule.span k[H] (Set.range v) := by
    rw [hv]
    exact Submodule.mem_top
  change x ∈ W
  have htransport : ∀ y : sigma.asModule,
      y ∈ Submodule.span k[H] (Set.range v) →
        rho.asModuleEquiv.symm (sigma.asModuleEquiv y) ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Submodule.subset_span (Set.mem_range_self i)
    | zero => simpa using W.zero_mem
    | add y z _hy _hz iy iz =>
        simpa using W.add_mem iy iz
    | smul r y _hy iy =>
        obtain ⟨s, hs⟩ := Finsupp.mapDomain_surjective hphi r
        have hsame :
            rho.asModuleEquiv.symm
                (sigma.asModuleEquiv (r • y)) =
              (inferInstance : SMul k[G] rho.asModule).smul s
                (rho.asModuleEquiv.symm (sigma.asModuleEquiv y)) := by
          apply rho.asModuleEquiv.injective
          rw [haction]
          simp only [LinearEquiv.apply_symm_apply, hs]
        rw [hsame]
        exact W.smul_mem s iy
  have := htransport xH hxH
  simpa only [xH, LinearEquiv.apply_symm_apply] using this

/-- Uniform subrepresentation generator bounds are unchanged by pullback
along a surjective homomorphism of acting groups. -/
theorem UniformSubrepresentationGeneratorBound.comp_of_surjective
    (sigma : Representation k H V) (phi : G →* H)
    (hphi : Function.Surjective phi) {n : ℕ}
    (hgen : UniformSubrepresentationGeneratorBound sigma n) :
    UniformSubrepresentationGeneratorBound (sigma.comp phi) n := by
  intro M
  let N : Subrepresentation sigma :=
    { toSubmodule := M.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        obtain ⟨g, rfl⟩ := hphi h
        exact M.apply_mem_toSubmodule g hx }
  have hN := hgen N
  have hpull := representationGeneratedBy_comp_of_surjective
    N.toRepresentation phi hphi hN
  simpa only [N, Subrepresentation.toRepresentation] using hpull

/-- In particular, a change by a group equivalence preserves every uniform
subrepresentation generator bound. -/
theorem UniformSubrepresentationGeneratorBound.comp_mulEquiv
    (sigma : Representation k H V) (e : G ≃* H) {n : ℕ}
    (hgen : UniformSubrepresentationGeneratorBound sigma n) :
    UniformSubrepresentationGeneratorBound
      (sigma.comp e.toMonoidHom) n :=
  hgen.comp_of_surjective sigma e.toMonoidHom e.surjective

/-- A uniform bound after restriction to a subgroup is already a uniform
bound for the original action. -/
theorem UniformSubrepresentationGeneratorBound.of_subgroup_restriction
    (rho : Representation k G V) (P : Subgroup G) {n : ℕ}
    (hgen : UniformSubrepresentationGeneratorBound
      (rho.comp P.subtype) n) :
    UniformSubrepresentationGeneratorBound rho n := by
  intro M
  let MP : Subrepresentation (rho.comp P.subtype) :=
    { toSubmodule := M.toSubmodule
      apply_mem_toSubmodule := fun g x hx ↦
        M.apply_mem_toSubmodule g.1 hx }
  apply representationGeneratedBy_of_subgroup_restriction P M.toRepresentation
  simpa only [MP, Subrepresentation.toRepresentation] using hgen MP

/-- Conjugating the subgroup of restriction preserves a uniform generator
bound.  The linear equivalence is the action of the conjugating element
itself. -/
theorem uniformSubrepresentationGeneratorBound_conjugate_restriction
    (rho : Representation k G V) (K : Subgroup G) (g : G) {n : ℕ}
    (hgen : UniformSubrepresentationGeneratorBound
      (rho.comp (MulAut.conj g • K : Subgroup G).subtype) n) :
    UniformSubrepresentationGeneratorBound
      (rho.comp K.subtype) n := by
  let rhoK : Representation k K V := rho.comp K.subtype
  let e : K ≃* (MulAut.conj g • K : Subgroup G) :=
    Subgroup.equivSMul (MulAut.conj g) K
  let sigma : Representation k K V :=
    (rho.comp (MulAut.conj g • K : Subgroup G).subtype).comp e.toMonoidHom
  have hsigma : UniformSubrepresentationGeneratorBound sigma n :=
    hgen.comp_mulEquiv
      (rho.comp (MulAut.conj g • K : Subgroup G).subtype) e
  let f : rhoK.IntertwiningMap sigma :=
    { toLinearMap := rho g
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro v
        change rho g (rho h.1 v) =
          rho ((e h : (MulAut.conj g • K : Subgroup G)) : G) (rho g v)
        rw [← Module.End.mul_apply, ← map_mul,
          ← Module.End.mul_apply, ← map_mul]
        change rho (g * h.1) v = rho (g * h.1 * g⁻¹ * g) v
        simp [mul_assoc] }
  have hbound : UniformSubrepresentationGeneratorBound rhoK n :=
    hsigma.of_injective f (rho.apply_bijective g).injective
  exact hbound

end SymmetricSubgroupAsymptotics

end
