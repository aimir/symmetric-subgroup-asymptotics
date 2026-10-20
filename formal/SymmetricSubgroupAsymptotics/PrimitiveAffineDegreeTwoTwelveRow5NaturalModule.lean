import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow5NaturalCoordinates
import SymmetricSubgroupAsymptotics.ModuleGeneratorMatrixPolynomialFibres
import SymmetricSubgroupAsymptotics.ModuleGeneratorPrincipalCoordinates
import SymmetricSubgroupAsymptotics.ModuleGeneratorUniformProjection
import SymmetricSubgroupAsymptotics.RepresentationModuleGeneratorTransport

/-! The exact row5 natural module is uniformly cyclic. On its augmentation,
two polynomial fibre generators occupy two matrix rows. Its block
constants are a cyclic polynomial module, and the actual ternary average
shares the one generator position across both summands. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow5NaturalModule

open PrimitiveAffineDegreeTwoTwelveRow5NaturalCoordinates

abbrev ActingRing := (ZMod 2)[Top]

def constantCoordinates : constants.asSubmodule ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  constantChart.equiv.symm

def augmentationCoordinates : augmentation.asSubmodule ≃ₗ[ZMod 2]
    (Fin 2 → Fin 4 → ZMod 2) :=
  augmentationChart.equiv.symm.trans rectangularCoordinates

private theorem constant_operator_action (x : constants.asSubmodule) :
    constantCoordinates.symm (constantOperator (constantCoordinates x)) =
      (MonoidAlgebra.single s 1 : ActingRing) • x := by
  apply Subtype.ext
  have hx : constantChart.inclusion (constantChart.coordinates x.1) = x.1 :=
    (constantChart.mem_iff _).mp x.property
  change constantChart.inclusion (constantOperator (constantChart.coordinates x.1)) =
    representation.asAlgebraHom (MonoidAlgebra.single s 1) x.1
  rw [Representation.asAlgebraHom_single, one_smul, ← constant_operator, hx]

theorem constants_uniform (W : Submodule ActingRing constants.asSubmodule) :
    ModuleGeneratedBy ActingRing W 1 := by
  refine ModuleGeneratedBy.one_of_polynomial_coordinates
    (R := ActingRing) (M := constants.asSubmodule) (K := ZMod 2)
    constantCoordinates.toAddEquiv constantOperator ?_ ?_ _
    constantWitness.polynomial_span W
  · intro S z x hx
    change constantCoordinates.symm (z • constantCoordinates x) ∈ S
    rw [map_smul, LinearEquiv.symm_apply_apply]
    exact S.smul_of_tower_mem z hx
  · intro S x hx
    change constantCoordinates.symm (constantOperator (constantCoordinates x)) ∈ S
    rw [constant_operator_action]
    exact S.smul_mem (MonoidAlgebra.single s 1) hx

private theorem augmentation_matrix_action (i j : Fin 2) (x : augmentation.asSubmodule) :
    augmentationCoordinates (matrixScalar i j • x) =
      Pi.single i (augmentationCoordinates x j) := by
  have hx : augmentationChart.inclusion (augmentationChart.coordinates x.1) = x.1 :=
    (augmentationChart.mem_iff _).mp x.property
  change rectangularCoordinates (augmentationChart.coordinates
      (representation.asAlgebraHom (matrixScalar i j) x.1)) =
    Pi.single i (rectangularCoordinates (augmentationChart.coordinates x.1) j)
  rw [← matrixOperator_eq]
  calc
    rectangularCoordinates (augmentationChart.coordinates (matrixOperator i j x.1)) =
        rectangularCoordinates (augmentationChart.coordinates
          (matrixOperator i j (augmentationChart.inclusion (augmentationChart.coordinates x.1)))) := by
      rw [hx]
    _ = rectangularCoordinates (matrixCoordinates i j (augmentationChart.coordinates x.1)) := by
      rw [matrix_action, augmentationChart.left_inverse]
    _ = Pi.single i (rectangularCoordinates (augmentationChart.coordinates x.1) j) :=
      rectangularCoordinates.apply_symm_apply _

private theorem augmentation_fibre_action (x : augmentation.asSubmodule) :
    augmentationCoordinates ((MonoidAlgebra.single s 1 ^ 2 : ActingRing) • x) =
      fun i ↦ fibreOperator (augmentationCoordinates x i) := by
  have hx : augmentationChart.inclusion (augmentationChart.coordinates x.1) = x.1 :=
    (augmentationChart.mem_iff _).mp x.property
  change rectangularCoordinates (augmentationChart.coordinates
      (representation.asAlgebraHom (MonoidAlgebra.single s 1 ^ 2) x.1)) =
    fun i ↦ fibreOperator (rectangularCoordinates (augmentationChart.coordinates x.1) i)
  rw [map_pow, Representation.asAlgebraHom_single, one_smul]
  calc
    rectangularCoordinates (augmentationChart.coordinates ((representation s ^ 2) x.1)) =
        rectangularCoordinates (augmentationChart.coordinates
          ((representation s ^ 2) (augmentationChart.inclusion (augmentationChart.coordinates x.1)))) := by
      rw [hx]
    _ = rectangularCoordinates (fibreCoordinates (augmentationChart.coordinates x.1)) := by
      rw [fibre_action, augmentationChart.left_inverse]
    _ = fun i ↦ fibreOperator (rectangularCoordinates (augmentationChart.coordinates x.1) i) :=
      rectangularCoordinates.apply_symm_apply _

theorem augmentation_uniform (W : Submodule ActingRing augmentation.asSubmodule) :
    ModuleGeneratedBy ActingRing W 1 :=
  ModuleGeneratedBy.one_of_matrixUnits_of_polynomial augmentationCoordinates
    matrixScalar augmentation_matrix_action (MonoidAlgebra.single s 1 ^ 2)
    fibreOperator augmentation_fibre_action _ fibreWitness.polynomial_span W

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
        projectionOperator (augmentationChart.inclusion (augmentationChart.coordinates x.1)) := by rw [hx]
    _ = 0 := PrimitiveAffineDegreeTwoTwelveRow5NaturalCoordinates.projection_augmentation _

private theorem pieces_sup : constants.asSubmodule ⊔ augmentation.asSubmodule = ⊤ := by
  apply top_unique
  intro x _
  apply Submodule.mem_sup.mpr
  refine ⟨constantChart.inclusion (constantChart.coordinates x), ?_,
    augmentationChart.inclusion (augmentationChart.coordinates x), ?_, decomposition x⟩
  · exact ⟨constantChart.coordinates x, rfl⟩
  · exact ⟨augmentationChart.coordinates x, rfl⟩

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Top (Fin 12)) 1 := by
  apply (uniformSubrepresentationGeneratorBound_iff_submodule representation 1).mpr
  exact ModuleGeneratedBy.uniform_of_projected_submodules
    constants.asSubmodule augmentation.asSubmodule projectionScalar
    projection_constants projection_augmentation pieces_sup 1
    constants_uniform augmentation_uniform

end PrimitiveAffineDegreeTwoTwelveRow5NaturalModule
end SymmetricSubgroupAsymptotics

end
