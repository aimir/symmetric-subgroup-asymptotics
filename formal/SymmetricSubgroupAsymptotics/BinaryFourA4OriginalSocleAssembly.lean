import SymmetricSubgroupAsymptotics.BinaryFourS4OriginalSocleAssembly
import SymmetricSubgroupAsymptotics.BinaryFourA4SixSlotEnvelope

/-! Assemble the original A4 target in its actual six-slot envelope.
The seventh S4 scalar is removed before using the cyclic bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourSymmetricBlockActions

private theorem six_projection_injective_on_support (x y : SymmetricEnvelope)
    (hx : x.1 2 = 0) (hy : y.1 2 = 0)
    (h : a4SixProjectionLinear x = a4SixProjectionLinear y) : x = y := by
  calc
    x = a4SixInclusionLinear (a4SixProjectionLinear x) := (a4SixInclusion_projection x hx).symm
    _ = a4SixInclusionLinear (a4SixProjectionLinear y) := congrArg a4SixInclusionLinear h
    _ = y := a4SixInclusion_projection y hy

theorem a4_original_socle_generated
    {G A : Type} [Group G] [AddCommGroup A] [_root_.Module Scalar A]
    (gamma : G →* Complement) (hgamma : Function.Surjective gamma)
    (rho : Representation Scalar G A)
    [IsSemisimpleModule Scalar[G] rho.asModule]
    (T : Subrepresentation rho)
    (S : OriginalMiddleSource (SemidirectProduct.inl.comp gamma) T.toRepresentation)
    (j : (rho.asModule ⧸ T.asSubmodule) →ₗ[Scalar[G]]
      (Representation.asModule (symmetricEnvelopeRepresentation.comp (SemidirectProduct.inl.comp gamma))))
    (hj : Function.Injective j)
    (htop : ∀ x, let y :=
      (Representation.asModuleEquiv (symmetricEnvelopeRepresentation.comp (SemidirectProduct.inl.comp gamma))) (j x)
      y.1 0 = 0 ∧ y.1 1 = 0 ∧ y.2.1 = 0)
    (hsix : ∀ x,
      ((Representation.asModuleEquiv (symmetricEnvelopeRepresentation.comp (SemidirectProduct.inl.comp gamma))) (j x)).1 2 = 0) :
    RepresentationGeneratedBy rho 2 := by
  let tau : Representation Scalar G SymmetricEnvelope := symmetricEnvelopeRepresentation.comp (SemidirectProduct.inl.comp gamma)
  let pi : G →* Ternary := (SemidirectProduct.rightHom : Complement →* Ternary).comp gamma
  let eta : Representation Scalar G A4SixSpace := a4SixCyclicRepresentation.comp pi
  let p : tau.IntertwiningMap eta := {
    toLinearMap := a4SixProjectionLinear
    isIntertwining' := fun g => a4SixProjection.isIntertwining' (gamma g) }
  let P : tau.asModule →ₗ[Scalar[G]] eta.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ p
  let q0 : S.sourceRepresentation.asModule →ₗ[Scalar[G]] T.toRepresentation.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ S.targetMap
  let eT : T.asSubmodule ≃ₗ[Scalar[G]] T.toRepresentation.asModule :=
    submoduleRepresentationModuleEquiv rho T.asSubmodule
  let q : S.sourceRepresentation.asModule →ₗ[Scalar[G]] T.asSubmodule := eT.symm.toLinearMap.comp q0
  have hq : Function.Surjective q := eT.symm.surjective.comp S.targetMap_surjective
  let i7 : S.sourceRepresentation.asModule →ₗ[Scalar[G]] tau.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ S.embedding
  let i := P.comp i7
  let j6 := P.comp j
  have hi : Function.Injective i := by
    intro x y h
    apply S.embedding_injective
    apply six_projection_injective_on_support _ _
      (S.middle_support (S.sourceRepresentation.asModuleEquiv x)).1
      (S.middle_support (S.sourceRepresentation.asModuleEquiv y)).1
    exact congrArg eta.asModuleEquiv h
  have hj6 : Function.Injective j6 := by
    intro x y h
    apply hj
    apply tau.asModuleEquiv.injective
    apply six_projection_injective_on_support _ _ (hsix x) (hsix y)
    exact congrArg eta.asModuleEquiv h
  have hd : Disjoint i.range j6.range := by
    apply Submodule.disjoint_def.mpr
    intro z hzI hzJ
    obtain ⟨x, rfl⟩ := hzI
    obtain ⟨y, hy⟩ := hzJ
    have ht := htop y
    have he := congrArg eta.asModuleEquiv hy
    have ht6 : (eta.asModuleEquiv (j6 y)).1 = 0 ∧ (eta.asModuleEquiv (j6 y)).2.1 = 0 := by
      constructor
      · ext k
        fin_cases k
        · exact ht.1
        · exact ht.2.1
      · exact ht.2.2
    rw [he] at ht6
    apply eta.asModuleEquiv.injective
    apply Prod.ext
    · exact ht6.1
    · exact Prod.ext ht6.2 (S.middle_support (S.sourceRepresentation.asModuleEquiv x)).2
  have hpi : Function.Surjective pi := by
    intro z
    obtain ⟨g, hg⟩ := hgamma (SemidirectProduct.inr z)
    exact ⟨g, congrArg SemidirectProduct.right hg⟩
  have hu : UniformSubrepresentationGeneratorBound eta 2 :=
    UniformSubrepresentationGeneratorBound.comp_of_surjective
      a4SixCyclicRepresentation pi hpi a4SixCyclic_uniform
  have hmodule : ∀ U : Submodule Scalar[G] eta.asModule, ModuleGeneratedBy Scalar[G] U 2 := by
    intro U
    exact ModuleGeneratedBy.congr (submoduleRepresentationModuleEquiv eta U).symm
      (hu (Subrepresentation.ofSubmodule' U))
  exact semisimple_extension_generated_of_common_envelope T.asSubmodule q hq i hi j6 hj6 hd 2 hmodule

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
