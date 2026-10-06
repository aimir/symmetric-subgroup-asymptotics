import SymmetricSubgroupAsymptotics.SchurKernelSectionHead

/-!
# Schur rows pulled through a section of a different target module

The action kernel of a simple model fixes every copy of that model in any
other module for the same group algebra.  This lets the kernel-section head
argument bound the multiplicity inside an actual invariant submodule, even
when the chosen simple model is displayed in a larger ambient module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {G B A V W : Type} [Group G] [Group B]
  [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The action kernel of one displayed simple model fixes the corresponding
isotypic component in every other module for the same group algebra. -/
theorem schurSimpleActionKernel_fixes_target_isotypic
    [FiniteDimensional (ZMod 2) V]
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (theta : Representation (ZMod 2) B V)
    (g : schurSimpleActionKernel sigma S)
    (y : isotypicComponent (ZMod 2)[B] theta.asModule S) :
    MonoidAlgebra.single (g : B) (1 : ZMod 2) • y = y := by
  let e := schurSocleDecomposition
    (k := ZMod 2) (R := (ZMod 2)[B]) (A := theta.asModule) (X := S)
  apply e.injective
  rw [e.map_smul]
  ext i
  exact congrArg Subtype.val
    ((mem_schurSimpleActionKernel_iff sigma S (g : B)).mp
      g.property (e y i))

/-- Dimension of an isotypic component in an arbitrary target module,
measured with a simple model displayed in a possibly different module. -/
theorem schur_target_isotypic_finrank_eq
    [FiniteDimensional (ZMod 2) A]
    [FiniteDimensional (ZMod 2) V]
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (theta : Representation (ZMod 2) B V) :
    Module.finrank (ZMod 2)
        ((isotypicComponent (ZMod 2)[B] theta.asModule S).restrictScalars
          (ZMod 2)) =
      Module.finrank (ZMod 2) S *
        schurSocleMultiplicity
          (k := ZMod 2) (R := (ZMod 2)[B])
          (A := theta.asModule) (X := S) := by
  letI : FiniteDimensional (ZMod 2) S :=
    FiniteDimensional.of_injective
      (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  let e := schurSocleDecomposition
    (k := ZMod 2) (R := (ZMod 2)[B]) (A := theta.asModule) (X := S)
  have he0 := ((Submodule.restrictScalarsEquiv
    (R := (ZMod 2)[B]) (M := theta.asModule) (ZMod 2)
      (isotypicComponent (ZMod 2)[B] theta.asModule S)).restrictScalars
        (ZMod 2)).finrank_eq
  have he1 := (e.restrictScalars (ZMod 2)).finrank_eq
  have he := he0.trans he1
  simpa [Module.finrank_pi_fintype, Nat.mul_comm] using he

/-- A uniform head bound on a representation section bounds the complete
isotypic row in its target, while the simple model and its action kernel may
be retained from a larger ambient representation. -/
theorem schurTargetIsotypic_finrank_le_of_kernel_section_head
    [Finite B] [FiniteDimensional (ZMod 2) A]
    [FiniteDimensional (ZMod 2) V]
    [FiniteDimensional (ZMod 2) W]
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (theta : Representation (ZMod 2) B V)
    (phi : G →* B)
    (K : Subgroup G)
    (hK : K = (schurSimpleActionKernel sigma S).comap phi)
    (tau : Representation (ZMod 2) G W)
    (M : Subrepresentation tau)
    (q : M.toRepresentation.IntertwiningMap (theta.comp phi))
    (hq : Function.Surjective q)
    (cap : ℕ)
    (hhead : BinaryUniformSubrepresentationHeadBound
      (tau.comp K.subtype) cap) :
    Module.finrank (ZMod 2) S *
        schurSocleMultiplicity
          (k := ZMod 2) (R := (ZMod 2)[B])
          (A := theta.asModule) (X := S) ≤ cap := by
  subst K
  let K := (schurSimpleActionKernel sigma S).comap phi
  let thetaPhi : Representation (ZMod 2) G V := theta.comp phi
  let I :=
    (isotypicComponent (ZMod 2)[B] theta.asModule S).restrictScalars
      (ZMod 2)
  let P : Submodule (ZMod 2) M.toSubmodule :=
    I.comap (theta.asModuleEquiv.symm.toLinearMap.comp q.toLinearMap)
  let M' : Subrepresentation (tau.comp K.subtype) := {
    toSubmodule := P.map M.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨v, hv, rfl⟩ := hv
      refine ⟨M.toRepresentation (g : G) v, ?_, rfl⟩
      change theta.asModuleEquiv.symm
          (q (M.toRepresentation (g : G) v)) ∈ I
      rw [Representation.IntertwiningMap.isIntertwining]
      have hfix := schurSimpleActionKernel_fixes_target_isotypic
        sigma S theta
        (⟨phi g, g.property⟩ : schurSimpleActionKernel sigma S)
        ⟨theta.asModuleEquiv.symm (q v), hv⟩
      have hfixModule := congrArg Subtype.val hfix
      have hfix' : theta (phi g) (q v) = q v := by
        calc
          theta (phi g) (q v) =
              theta.asModuleEquiv
                (MonoidAlgebra.single (phi g) (1 : ZMod 2) •
                  theta.asModuleEquiv.symm (q v)) := by
            rw [Representation.asModuleEquiv_map_smul,
              Representation.asAlgebraHom_single, one_smul,
              LinearEquiv.apply_symm_apply]
          _ = theta.asModuleEquiv (theta.asModuleEquiv.symm (q v)) :=
            congrArg theta.asModuleEquiv hfixModule
          _ = q v := rfl
      rw [show thetaPhi g (q v) = q v by exact hfix']
      exact hv }
  let e : P ≃ₗ[ZMod 2] M'.toSubmodule :=
    M.toSubmodule.equivSubtypeMap P
  let qP : P →ₗ[ZMod 2] I :=
    ((theta.asModuleEquiv.symm.toLinearMap.comp q.toLinearMap).comp
      P.subtype)
      |>.codRestrict I (fun v ↦ v.property)
  have hqP : Function.Surjective qP := by
    intro z
    obtain ⟨v, hv⟩ := hq (theta.asModuleEquiv z.1)
    have hvP : v ∈ P := by
      change theta.asModuleEquiv.symm (q v) ∈ I
      rw [hv, LinearEquiv.symm_apply_apply]
      exact z.property
    refine ⟨⟨v, hvP⟩, Subtype.ext ?_⟩
    change theta.asModuleEquiv.symm (q v) = z.1
    rw [hv, LinearEquiv.symm_apply_apply]
  let qM : M'.toSubmodule →ₗ[ZMod 2] I :=
    qP.comp e.symm.toLinearMap
  have hqM : Function.Surjective qM := hqP.comp e.symm.surjective
  have htrivial : ∀ (g : K) (m : M'.toSubmodule),
      qM (M'.toRepresentation g m) = qM m := by
    intro g m
    apply Subtype.ext
    change theta.asModuleEquiv.symm
        (q (e.symm (M'.toRepresentation g m) : M.toSubmodule)) =
      theta.asModuleEquiv.symm (q (e.symm m : M.toSubmodule))
    have he : (e.symm (M'.toRepresentation g m) : M.toSubmodule) =
        M.toRepresentation (g : G) (e.symm m : M.toSubmodule) := by
      apply Subtype.ext
      rfl
    rw [he, Representation.IntertwiningMap.isIntertwining]
    have hfix := schurSimpleActionKernel_fixes_target_isotypic
      sigma S theta
      (⟨phi g, g.property⟩ : schurSimpleActionKernel sigma S)
      ⟨theta.asModuleEquiv.symm (q (e.symm m : M.toSubmodule)),
        (e.symm m).property⟩
    have hfixModule := congrArg Subtype.val hfix
    have hfix' : theta (phi g) (q (e.symm m : M.toSubmodule)) =
        q (e.symm m : M.toSubmodule) := by
      calc
        theta (phi g) (q (e.symm m : M.toSubmodule)) =
            theta.asModuleEquiv
              (MonoidAlgebra.single (phi g) (1 : ZMod 2) •
                theta.asModuleEquiv.symm
                  (q (e.symm m : M.toSubmodule))) := by
          rw [Representation.asModuleEquiv_map_smul,
            Representation.asAlgebraHom_single, one_smul,
            LinearEquiv.apply_symm_apply]
        _ = theta.asModuleEquiv
              (theta.asModuleEquiv.symm
                (q (e.symm m : M.toSubmodule))) :=
          congrArg theta.asModuleEquiv hfixModule
        _ = q (e.symm m : M.toSubmodule) := rfl
    exact congrArg theta.asModuleEquiv.symm hfix'
  let q' : M'.toRepresentation.Coinvariants →ₗ[ZMod 2] I :=
    Representation.Coinvariants.lift M'.toRepresentation qM (by
      intro g
      apply LinearMap.ext
      exact htrivial g)
  have hq' : Function.Surjective q' := by
    intro z
    obtain ⟨m, hm⟩ := hqM z
    exact ⟨Representation.Coinvariants.mk M'.toRepresentation m, hm⟩
  letI : FiniteDimensional (ZMod 2) M'.toSubmodule :=
    FiniteDimensional.of_injective
      (M'.toSubmodule.subtype.restrictScalars (ZMod 2))
      M'.toSubmodule.subtype_injective
  have hdim : Module.finrank (ZMod 2) I ≤
      Module.finrank (ZMod 2) M'.toRepresentation.Coinvariants :=
    LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  rw [← schur_target_isotypic_finrank_eq sigma S theta]
  exact hdim.trans (hhead M')

end SymmetricSubgroupAsymptotics

end
