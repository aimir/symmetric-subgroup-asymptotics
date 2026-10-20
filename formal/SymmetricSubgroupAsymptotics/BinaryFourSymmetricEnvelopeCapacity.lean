import SymmetricSubgroupAsymptotics.BinaryFourSymmetricEnvelopeTraceAlgebra
import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads

/-! Uniform two-generation of the actual S4 seven-dimensional envelope.
The ternary trace separates the two literal components, so their two
positions are shared rather than added. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourSymmetricBlockActions

private abbrev R := Scalar[SymmetricComplement]
private abbrev rho := symmetricEnvelopeRepresentation

private def trivialMap : rho.asModule →ₗ[R] trivialEnvelopeRepresentation.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _ symmetricEnvelopeTrivialProjection

private def activeMap : rho.asModule →ₗ[R] activeEnvelopeRepresentation.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _ symmetricEnvelopeActiveProjection

private theorem trivialMap_injective_on_active_kernel
    (U : Submodule R rho.asModule) (hU : U ≤ activeMap.ker) :
    Function.Injective (fun x : U => trivialMap x.1) := by
  intro x y h
  apply Subtype.ext
  apply rho.asModuleEquiv.injective
  apply Prod.ext
  · exact congrArg trivialEnvelopeRepresentation.asModuleEquiv h
  · have hx := hU x.2
    have hy := hU y.2
    have hx' := congrArg activeEnvelopeRepresentation.asModuleEquiv hx
    have hy' := congrArg activeEnvelopeRepresentation.asModuleEquiv hy
    exact hx'.trans hy'.symm

private theorem activeMap_injective_on_trivial_kernel
    (U : Submodule R rho.asModule) (hU : U ≤ trivialMap.ker) :
    Function.Injective (fun x : U => activeMap x.1) := by
  intro x y h
  apply Subtype.ext
  apply rho.asModuleEquiv.injective
  apply Prod.ext
  · have hx := hU x.2
    have hy := hU y.2
    have hx' := congrArg trivialEnvelopeRepresentation.asModuleEquiv hx
    have hy' := congrArg trivialEnvelopeRepresentation.asModuleEquiv hy
    exact hx'.trans hy'.symm
  · exact congrArg activeEnvelopeRepresentation.asModuleEquiv h

private theorem trivial_kernel_component_generated
    (U : Submodule R rho.asModule) (hU : U ≤ activeMap.ker) :
    ModuleGeneratedBy R U 2 := by
  let E : Subrepresentation rho := Subrepresentation.ofSubmodule' U
  let f : E.toRepresentation.IntertwiningMap trivialEnvelopeRepresentation :=
    symmetricEnvelopeTrivialProjection.comp {
      toLinearMap := E.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    have hinj := trivialMap_injective_on_active_kernel U hU
    have heq : trivialMap (x : SymmetricEnvelope) = trivialMap (y : SymmetricEnvelope) := by
      exact congrArg trivialEnvelopeRepresentation.asModuleEquiv.symm h
    exact hinj heq
  have hg := representationGeneratedBy_of_injective_of_uniform
    trivialEnvelope_uniform f hf
  exact ModuleGeneratedBy.congr (submoduleRepresentationModuleEquiv rho U).symm hg

private theorem active_kernel_component_generated
    (U : Submodule R rho.asModule) (hU : U ≤ trivialMap.ker) :
    ModuleGeneratedBy R U 2 := by
  let E : Subrepresentation rho := Subrepresentation.ofSubmodule' U
  let f : E.toRepresentation.IntertwiningMap activeEnvelopeRepresentation :=
    symmetricEnvelopeActiveProjection.comp {
      toLinearMap := E.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    have hinj := activeMap_injective_on_trivial_kernel U hU
    have heq : activeMap (x : SymmetricEnvelope) = activeMap (y : SymmetricEnvelope) := by
      exact congrArg activeEnvelopeRepresentation.asModuleEquiv.symm h
    exact hinj heq
  have hg := representationGeneratedBy_of_injective_of_uniform
    activeEnvelope_uniform f hf
  exact ModuleGeneratedBy.congr (submoduleRepresentationModuleEquiv rho U).symm hg

/-- Every invariant subspace of the full S4 envelope uses two slots,
including the sign-type top case. -/
theorem symmetricEnvelope_uniform :
    UniformSubrepresentationGeneratorBound symmetricEnvelopeRepresentation 2 := by
  intro E
  letI : _root_.Module R rho.asModule :=
    Representation.instModuleMonoidAlgebraAsModule rho
  have hW : ModuleGeneratedBy R E.asSubmodule 2 := by
    apply @ModuleGeneratedBy.uniform_of_projector R rho.asModule inferInstance inferInstance
      (Representation.instModuleMonoidAlgebraAsModule rho) activeMap.ker trivialMap.ker
      envelopeTraceAlgebra 2
    · intro x
      apply rho.asModuleEquiv.injective
      rw [envelopeTraceAlgebra_smul]
      apply Prod.ext
      · rfl
      · have h := congrArg activeEnvelopeRepresentation.asModuleEquiv x.2
        exact h.symm
    · intro x
      apply rho.asModuleEquiv.injective
      rw [envelopeTraceAlgebra_smul]
      have h := congrArg trivialEnvelopeRepresentation.asModuleEquiv x.2
      exact Prod.ext h rfl
    · intro x
      change activeMap (envelopeTraceAlgebra • x) = 0
      apply activeEnvelopeRepresentation.asModuleEquiv.injective
      change (rho.asModuleEquiv (envelopeTraceAlgebra • x)).2 = 0
      rw [envelopeTraceAlgebra_smul]
      rfl
    · intro x
      change trivialMap (x - envelopeTraceAlgebra • x) = 0
      apply trivialEnvelopeRepresentation.asModuleEquiv.injective
      change (rho.asModuleEquiv (x - envelopeTraceAlgebra • x)).1 = 0
      rw [map_sub, envelopeTraceAlgebra_smul]
      exact sub_self _
    · exact trivial_kernel_component_generated
    · exact active_kernel_component_generated
  exact ModuleGeneratedBy.congr (submoduleRepresentationModuleEquiv rho E.asSubmodule) hW

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
