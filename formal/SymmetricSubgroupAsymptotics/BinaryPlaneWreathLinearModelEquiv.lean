import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathUniform
import SymmetricSubgroupAsymptotics.BinaryPlaneWreathNormalGenerators
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! Exact conversion between pointwise multiplicative binary-plane affine
coordinates and the additive function-module semidirect model. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneWreathLinearModelEquiv
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open LinearSemidirectCoprimeSocleBounds

variable {R I : Type} [Group R] [MulAction R I] [Fintype I] [DecidableEq I]

abbrev fullRepresentation := PermutationalWreathProduct.functionRepresentation
  (Q := R) (I := I) BinaryPlaneCyclicWreathUniform.localRepresentation

def linear : W (R := R) (I := I) →* ((I → Plane) ≃ₗ[ZMod 2] (I → Plane)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (I → Plane)).toMonoidHom.comp
    (fullRepresentation (R := R) (I := I)).asGroupHom

abbrev AdditiveModel := Model (linear (R := R) (I := I))
abbrev PointwiseModel := BinaryPlaneWreathNormalGenerators.Model (R := R) (I := I)

def toAdditive : PointwiseModel (R := R) (I := I) →* AdditiveModel (R := R) (I := I) where
  toFun g := ⟨Multiplicative.ofAdd (fun i => (g.left i).toAdd),g.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      rfl
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      rfl
    · rfl

def equiv : PointwiseModel (R := R) (I := I) ≃* AdditiveModel (R := R) (I := I) :=
  MulEquiv.ofBijective (toAdditive (R := R) (I := I)) ⟨by
    intro g h he
    apply SemidirectProduct.ext
    · funext i
      exact congrArg (fun z : AdditiveModel (R := R) (I := I) =>
        Multiplicative.ofAdd (z.left.toAdd i)) he
    · exact congrArg (fun z : AdditiveModel (R := R) (I := I) => z.right) he,
    by
      intro g
      refine ⟨(⟨fun i => Multiplicative.ofAdd (g.left.toAdd i),g.right⟩ :
        PointwiseModel (R := R) (I := I)),?_⟩
      apply SemidirectProduct.ext <;> rfl⟩

@[simp] theorem linearRepresentation_eq :
    linearRepresentation (linear (R := R) (I := I))=fullRepresentation := rfl

end SymmetricSubgroupAsymptotics.BinaryPlaneWreathLinearModelEquiv
