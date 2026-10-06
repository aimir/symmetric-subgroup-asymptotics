import SymmetricSubgroupAsymptotics.Non2SchurMixedSocleDimension
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead

/-!
# A Schur row pulled through an actual representation section

Let a representation `sigma` be a quotient of a subrepresentation of an
ambient representation `tau`.  The action kernel of a selected simple row
fixes the complete isotypic component pointwise.  Pulling that component
back through the literal quotient therefore realizes it as a trivial
quotient of a subrepresentation of `tau` restricted to the row kernel.

This is the representation-theoretic plumbing used by the exceptional
degree-four scalar rows.  It keeps the original section map and does not
embed the quotient back into the ambient induced module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {G B A V : Type} [Group G] [Group B]
  [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Uniform binary head bound on every subrepresentation of one literal
representation.  Naming this predicate keeps the Schur section theorem's
dependent kernel signature small enough to elaborate predictably. -/
def BinaryUniformSubrepresentationHeadBound
    {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (rho : Representation (ZMod 2) G W) (cap : ℕ) : Prop :=
  ∀ T : Subrepresentation rho,
    Module.finrank (ZMod 2)
      (T.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ cap

/-- A uniform head bound after restriction to the selected row kernel
bounds the entire selected isotypic component of an actual quotient
section.  The left side is subsequently identified with `h * m` by the
literal Schur decomposition. -/
theorem schurIsotypic_finrank_le_of_kernel_section_head
    [Finite B] [FiniteDimensional (ZMod 2) A]
    [FiniteDimensional (ZMod 2) V]
    (sigma : Representation (ZMod 2) B A)
    (T : Subrepresentation sigma)
    [IsSimpleModule (ZMod 2)[B] T.asSubmodule]
    (phi : G →* B)
    (K : Subgroup G)
    (hK : K = (schurSimpleActionKernel sigma T.asSubmodule).comap phi)
    (tau : Representation (ZMod 2) G V)
    (M : Subrepresentation tau)
    (q : M.toRepresentation.IntertwiningMap (sigma.comp phi))
    (hq : Function.Surjective q)
    (cap : ℕ)
    (hhead : BinaryUniformSubrepresentationHeadBound
      (tau.comp K.subtype) cap) :
    Module.finrank (ZMod 2) T.asSubmodule *
        schurSocleMultiplicity
          (k := ZMod 2) (R := (ZMod 2)[B])
          (A := sigma.asModule) (X := T.asSubmodule) ≤ cap := by
  subst K
  let S := T.asSubmodule
  let K := (schurSimpleActionKernel sigma S).comap phi
  let sigmaPhi : Representation (ZMod 2) G A := sigma.comp phi
  let W :=
    (isotypicComponent (ZMod 2)[B] sigma.asModule S).restrictScalars (ZMod 2)
  let P : Submodule (ZMod 2) M.toSubmodule :=
    W.comap (sigma.asModuleEquiv.symm.toLinearMap.comp q.toLinearMap)
  let M' : Subrepresentation (tau.comp K.subtype) := {
    toSubmodule := P.map M.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨v, hv, rfl⟩ := hv
      refine ⟨M.toRepresentation (g : G) v, ?_, rfl⟩
      change sigma.asModuleEquiv.symm
          (q (M.toRepresentation (g : G) v)) ∈ W
      rw [Representation.IntertwiningMap.isIntertwining]
      have hfix := schurSimpleActionKernel_fixes_isotypic sigma S
        (⟨phi g, g.property⟩ : schurSimpleActionKernel sigma S)
        ⟨sigma.asModuleEquiv.symm (q v), hv⟩
      have hfixModule := congrArg Subtype.val hfix
      have hfix' : sigma (phi g) (q v) = q v := by
        calc
          sigma (phi g) (q v) =
              sigma.asModuleEquiv
                (MonoidAlgebra.single (phi g) (1 : ZMod 2) •
                  sigma.asModuleEquiv.symm (q v)) := by
            rw [Representation.asModuleEquiv_map_smul,
              Representation.asAlgebraHom_single, one_smul,
              LinearEquiv.apply_symm_apply]
          _ = sigma.asModuleEquiv (sigma.asModuleEquiv.symm (q v)) :=
            congrArg sigma.asModuleEquiv hfixModule
          _ = q v := rfl
      rw [show sigmaPhi g (q v) = q v by exact hfix']
      exact hv }
  let e : P ≃ₗ[ZMod 2] M'.toSubmodule :=
    M.toSubmodule.equivSubtypeMap P
  let qP : P →ₗ[ZMod 2] W :=
    ((sigma.asModuleEquiv.symm.toLinearMap.comp q.toLinearMap).comp
      P.subtype)
      |>.codRestrict W (fun v ↦ v.property)
  have hqP : Function.Surjective qP := by
    intro w
    obtain ⟨v, hv⟩ := hq (sigma.asModuleEquiv w.1)
    have hvP : v ∈ P := by
      change sigma.asModuleEquiv.symm (q v) ∈ W
      rw [hv, LinearEquiv.symm_apply_apply]
      exact w.property
    refine ⟨⟨v, hvP⟩, Subtype.ext ?_⟩
    change sigma.asModuleEquiv.symm (q v) = w.1
    rw [hv, LinearEquiv.symm_apply_apply]
  let qM : M'.toSubmodule →ₗ[ZMod 2] W :=
    qP.comp e.symm.toLinearMap
  have hqM : Function.Surjective qM := hqP.comp e.symm.surjective
  have htrivial : ∀ (g : K) (m : M'.toSubmodule),
      qM (M'.toRepresentation g m) = qM m := by
    intro g m
    apply Subtype.ext
    change sigma.asModuleEquiv.symm
        (q (e.symm (M'.toRepresentation g m) : M.toSubmodule)) =
      sigma.asModuleEquiv.symm (q (e.symm m : M.toSubmodule))
    have he : (e.symm (M'.toRepresentation g m) : M.toSubmodule) =
        M.toRepresentation (g : G) (e.symm m : M.toSubmodule) := by
      apply Subtype.ext
      rfl
    rw [he, Representation.IntertwiningMap.isIntertwining]
    have hfix := schurSimpleActionKernel_fixes_isotypic sigma S
      (⟨phi g, g.property⟩ : schurSimpleActionKernel sigma S)
      ⟨sigma.asModuleEquiv.symm (q (e.symm m : M.toSubmodule)),
        (e.symm m).property⟩
    have hfixModule := congrArg Subtype.val hfix
    have hfix' : sigma (phi g) (q (e.symm m : M.toSubmodule)) =
        q (e.symm m : M.toSubmodule) := by
      calc
        sigma (phi g) (q (e.symm m : M.toSubmodule)) =
            sigma.asModuleEquiv
              (MonoidAlgebra.single (phi g) (1 : ZMod 2) •
                sigma.asModuleEquiv.symm
                  (q (e.symm m : M.toSubmodule))) := by
          rw [Representation.asModuleEquiv_map_smul,
            Representation.asAlgebraHom_single, one_smul,
            LinearEquiv.apply_symm_apply]
        _ = sigma.asModuleEquiv
              (sigma.asModuleEquiv.symm
                (q (e.symm m : M.toSubmodule))) :=
          congrArg sigma.asModuleEquiv hfixModule
        _ = q (e.symm m : M.toSubmodule) := rfl
    exact congrArg sigma.asModuleEquiv.symm hfix'
  let q' : M'.toRepresentation.Coinvariants →ₗ[ZMod 2] W :=
    Representation.Coinvariants.lift M'.toRepresentation qM (by
      intro g
      apply LinearMap.ext
      exact htrivial g)
  have hq' : Function.Surjective q' := by
    intro w
    obtain ⟨m, hm⟩ := hqM w
    exact ⟨Representation.Coinvariants.mk M'.toRepresentation m, hm⟩
  letI : FiniteDimensional (ZMod 2) M'.toSubmodule :=
    FiniteDimensional.of_injective
      (M'.toSubmodule.subtype.restrictScalars (ZMod 2))
      M'.toSubmodule.subtype_injective
  have hdim : Module.finrank (ZMod 2) W ≤
      Module.finrank (ZMod 2) M'.toRepresentation.Coinvariants :=
    LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  rw [← schur_isotypic_finrank_eq sigma S]
  exact hdim.trans (hhead M')

end SymmetricSubgroupAsymptotics

end
