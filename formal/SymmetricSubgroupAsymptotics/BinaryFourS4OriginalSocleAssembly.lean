import SymmetricSubgroupAsymptotics.BinaryFourOriginalMiddleSource
import SymmetricSubgroupAsymptotics.SemisimpleExtensionCommonEnvelopeCapacity
import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads

/-! Assemble the actual semisimple target from its literal middle
source and its literal top quotient map, in the unchanged S4 envelope. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourSymmetricBlockActions

variable {G A : Type} [Group G] [AddCommGroup A] [_root_.Module Scalar A]

theorem s4_original_socle_generated
    (gamma : G →* SymmetricComplement) (hgamma : Function.Surjective gamma)
    (rho : Representation Scalar G A)
    [IsSemisimpleModule Scalar[G] rho.asModule]
    (T : Subrepresentation rho)
    (S : OriginalMiddleSource gamma T.toRepresentation)
    (j : (rho.asModule ⧸ T.asSubmodule) →ₗ[Scalar[G]]
      (Representation.asModule (symmetricEnvelopeRepresentation.comp gamma)))
    (hj : Function.Injective j)
    (htop : ∀ x, let y := (Representation.asModuleEquiv (symmetricEnvelopeRepresentation.comp gamma)) (j x)
      y.1 0 = 0 ∧ y.1 1 = 0 ∧ y.2.1 = 0) :
    RepresentationGeneratedBy rho 2 := by
  let tau : Representation Scalar G SymmetricEnvelope := symmetricEnvelopeRepresentation.comp gamma
  let q0 : S.sourceRepresentation.asModule →ₗ[Scalar[G]] T.toRepresentation.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ S.targetMap
  let eT : T.asSubmodule ≃ₗ[Scalar[G]] T.toRepresentation.asModule :=
    submoduleRepresentationModuleEquiv rho T.asSubmodule
  let q : S.sourceRepresentation.asModule →ₗ[Scalar[G]] T.asSubmodule :=
    eT.symm.toLinearMap.comp q0
  have hq : Function.Surjective q := eT.symm.surjective.comp S.targetMap_surjective
  let i : S.sourceRepresentation.asModule →ₗ[Scalar[G]] tau.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ S.embedding
  have hi : Function.Injective i := S.embedding_injective
  have hd : Disjoint i.range j.range := by
    apply Submodule.disjoint_def.mpr
    intro z hzI hzJ
    obtain ⟨x, rfl⟩ := hzI
    obtain ⟨y, hy⟩ := hzJ
    apply tau.asModuleEquiv.injective
    change S.embedding (S.sourceRepresentation.asModuleEquiv x) = 0
    have hm := S.middle_support (S.sourceRepresentation.asModuleEquiv x)
    have ht := htop y
    have he := congrArg tau.asModuleEquiv hy
    change tau.asModuleEquiv (j y) = S.embedding (S.sourceRepresentation.asModuleEquiv x) at he
    rw [he] at ht
    apply Prod.ext
    · ext k
      fin_cases k
      · exact ht.1
      · exact ht.2.1
      · exact hm.1
    · exact Prod.ext ht.2.2 hm.2
  have hu : UniformSubrepresentationGeneratorBound tau 2 :=
    UniformSubrepresentationGeneratorBound.comp_of_surjective
      symmetricEnvelopeRepresentation gamma hgamma symmetricEnvelope_uniform
  have hmodule : ∀ U : Submodule Scalar[G] tau.asModule,
      ModuleGeneratedBy Scalar[G] U 2 := by
    intro U
    exact ModuleGeneratedBy.congr (submoduleRepresentationModuleEquiv tau U).symm
      (hu (Subrepresentation.ofSubmodule' U))
  exact semisimple_extension_generated_of_common_envelope T.asSubmodule q hq i hi j hj hd 2 hmodule

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
