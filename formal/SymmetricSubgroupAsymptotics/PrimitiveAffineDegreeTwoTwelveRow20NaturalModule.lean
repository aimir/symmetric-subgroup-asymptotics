import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow20NaturalCoordinates
import SymmetricSubgroupAsymptotics.ModuleGeneratorPrincipalCoordinates
import SymmetricSubgroupAsymptotics.ModuleGeneratorUniformProjection
import SymmetricSubgroupAsymptotics.RepresentationModuleGeneratorTransport

/-! The literal row20 natural module is uniformly cyclic. The actual
ternary projector separates four binary coordinates from four quadratic
coordinates. On both pieces the same local alternating operator is
cyclic over the appropriate polynomial ring. Quadratic scalars are
realized by the original central three-cycle, so this bounds every
original invariant submodule. The projector shares one generator slot. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow20NaturalModule

open PrimitiveAffineDegreeTwoTwelveRow20NaturalCoordinates

abbrev ActingRing := (ZMod 2)[Top]

def constantCoordinates : constants.asSubmodule ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  constantChart.equiv.symm

def quadraticCoordinates : augmentation.asSubmodule ≃ₗ[ZMod 2] (Fin 4 → Scalar) :=
  augmentationChart.equiv.symm.trans fieldCoordinates

private theorem constant_operator_action (x : constants.asSubmodule) :
    constantCoordinates.symm
      (BinaryLocalAlternatingFourPolynomial.operator (ZMod 2) (constantCoordinates x)) =
      operatorScalar • x := by
  apply Subtype.ext
  have hx : constantChart.inclusion (constantChart.coordinates x.1) = x.1 :=
    (constantChart.mem_iff _).mp x.property
  change constantChart.inclusion
      (BinaryLocalAlternatingFourPolynomial.operator (ZMod 2)
        (constantChart.coordinates x.1)) =
    representation.asAlgebraHom operatorScalar x.1
  rw [← operator_eq, ← constant_operator, hx]

private theorem quadratic_operator_action (x : augmentation.asSubmodule) :
    quadraticCoordinates.symm
      (BinaryLocalAlternatingFourPolynomial.operator Scalar (quadraticCoordinates x)) =
      operatorScalar • x := by
  apply Subtype.ext
  have hx : augmentationChart.inclusion (augmentationChart.coordinates x.1) = x.1 :=
    (augmentationChart.mem_iff _).mp x.property
  change augmentationChart.inclusion
      (coordinateOperator (augmentationChart.coordinates x.1)) =
    representation.asAlgebraHom operatorScalar x.1
  rw [← operator_eq, ← augmentation_operator, hx]

private theorem quadratic_omega_action (x : augmentation.asSubmodule) :
    quadraticCoordinates.symm (BinaryQuadraticField.omega • quadraticCoordinates x) =
      (MonoidAlgebra.single c⁻¹ 1 : ActingRing) • x := by
  apply Subtype.ext
  have hx : augmentationChart.inclusion (augmentationChart.coordinates x.1) = x.1 :=
    (augmentationChart.mem_iff _).mp x.property
  change augmentationChart.inclusion
      (omegaOperator (augmentationChart.coordinates x.1)) =
    representation.asAlgebraHom (MonoidAlgebra.single c⁻¹ 1) x.1
  rw [Representation.asAlgebraHom_single, one_smul, ← omega_apply, hx]

private theorem quadratic_scalar_action (z : Scalar) (x : augmentation.asSubmodule) :
    quadraticCoordinates.symm (z • quadraticCoordinates x) =
      z.re • x + z.im • quadraticCoordinates.symm
        (BinaryQuadraticField.omega • quadraticCoordinates x) := by
  apply quadraticCoordinates.injective
  rw [quadraticCoordinates.apply_symm_apply, map_add,
    quadraticCoordinates.map_smul z.re x, quadraticCoordinates.map_smul z.im _,
    quadraticCoordinates.apply_symm_apply]
  calc
    z • quadraticCoordinates x =
        (z.re • (1 : Scalar) + z.im • BinaryQuadraticField.omega) • quadraticCoordinates x :=
      congrArg (fun t : Scalar ↦ t • quadraticCoordinates x) (BinaryQuadraticField.scalar_eq z)
    _ = z.re • quadraticCoordinates x +
        z.im • (BinaryQuadraticField.omega • quadraticCoordinates x) := by
      rw [add_smul]
      simp only [smul_assoc, one_smul]

theorem constants_uniform (W : Submodule ActingRing constants.asSubmodule) :
    ModuleGeneratedBy ActingRing W 1 := by
  refine ModuleGeneratedBy.one_of_polynomial_coordinates
    (R := ActingRing) (M := constants.asSubmodule) (K := ZMod 2)
    constantCoordinates.toAddEquiv
    (BinaryLocalAlternatingFourPolynomial.operator (ZMod 2)) ?_ ?_ _
    BinaryLocalAlternatingFourPolynomial.binaryWitness.polynomial_span W
  · intro S z x hx
    change constantCoordinates.symm (z • constantCoordinates x) ∈ S
    rw [map_smul, LinearEquiv.symm_apply_apply]
    exact S.smul_of_tower_mem z hx
  · intro S x hx
    change constantCoordinates.symm
      (BinaryLocalAlternatingFourPolynomial.operator (ZMod 2) (constantCoordinates x)) ∈ S
    rw [constant_operator_action]
    exact S.smul_mem operatorScalar hx

theorem augmentation_uniform (W : Submodule ActingRing augmentation.asSubmodule) :
    ModuleGeneratedBy ActingRing W 1 := by
  refine ModuleGeneratedBy.one_of_polynomial_coordinates
    (R := ActingRing) (M := augmentation.asSubmodule) (K := Scalar)
    quadraticCoordinates.toAddEquiv
    (BinaryLocalAlternatingFourPolynomial.operator Scalar) ?_ ?_ _
    BinaryLocalAlternatingFourPolynomial.quadraticWitness.polynomial_span W
  · intro S z x hx
    change quadraticCoordinates.symm (z • quadraticCoordinates x) ∈ S
    rw [quadratic_scalar_action, quadratic_omega_action]
    exact S.add_mem (S.smul_of_tower_mem z.re hx)
      (S.smul_of_tower_mem z.im (S.smul_mem (MonoidAlgebra.single c⁻¹ 1) hx))
  · intro S x hx
    change quadraticCoordinates.symm
      (BinaryLocalAlternatingFourPolynomial.operator Scalar (quadraticCoordinates x)) ∈ S
    rw [quadratic_operator_action]
    exact S.smul_mem operatorScalar hx

private theorem projection_constants (x : constants.asSubmodule) :
    projectionScalar • (x : representation.asModule) = x := by
  have hx : constantChart.inclusion (constantChart.coordinates x.1) = x.1 :=
    (constantChart.mem_iff _).mp x.property
  change representation.asAlgebraHom projectionScalar x.1 = x.1
  rw [← projectionOperator_eq]
  calc
    projectionOperator x.1 =
        projectionOperator (constantChart.inclusion (constantChart.coordinates x.1)) := by rw [hx]
    _ = constantChart.inclusion (constantChart.coordinates x.1) := projection_constant _
    _ = x.1 := hx

private theorem projection_augmentation (x : augmentation.asSubmodule) :
    projectionScalar • (x : representation.asModule) = 0 := by
  have hx : augmentationChart.inclusion (augmentationChart.coordinates x.1) = x.1 :=
    (augmentationChart.mem_iff _).mp x.property
  change representation.asAlgebraHom projectionScalar x.1 = 0
  rw [← projectionOperator_eq]
  calc
    projectionOperator x.1 =
        projectionOperator (augmentationChart.inclusion (augmentationChart.coordinates x.1)) := by
      rw [hx]
    _ = 0 := PrimitiveAffineDegreeTwoTwelveRow20NaturalCoordinates.projection_augmentation _

private theorem pieces_sup : constants.asSubmodule ⊔ augmentation.asSubmodule = ⊤ := by
  apply top_unique
  intro x _
  apply Submodule.mem_sup.mpr
  refine ⟨constantChart.inclusion (constantChart.coordinates x), ?_,
    augmentationChart.inclusion (augmentationChart.coordinates x), ?_, decomposition x⟩
  · exact ⟨constantChart.coordinates x, rfl⟩
  · exact ⟨augmentationChart.coordinates x, rfl⟩

/-- The exact original row20 natural module has uniform generator bound
one, including invariant submodules meeting both projected summands. -/
theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Top (Fin 12)) 1 := by
  apply (uniformSubrepresentationGeneratorBound_iff_submodule representation 1).mpr
  exact ModuleGeneratedBy.uniform_of_projected_submodules
    constants.asSubmodule augmentation.asSubmodule projectionScalar
    projection_constants projection_augmentation pieces_sup 1
    constants_uniform augmentation_uniform

end PrimitiveAffineDegreeTwoTwelveRow20NaturalModule
end SymmetricSubgroupAsymptotics

end
