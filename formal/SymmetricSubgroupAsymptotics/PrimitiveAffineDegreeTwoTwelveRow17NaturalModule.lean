import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow17NaturalCoordinates
import SymmetricSubgroupAsymptotics.ModuleGeneratorMatrixUnits
import SymmetricSubgroupAsymptotics.ModuleGeneratorUniformProjection
import SymmetricSubgroupAsymptotics.RepresentationModuleGeneratorTransport

/-! Every invariant subspace of the literal row-17 natural binary module
is cyclic. The proof uses matrix units on its eight-dimensional
augmentation, a cyclic polynomial module on the four block constants,
and the actual group-algebra projector separating these two parts. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial BigOperators

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow17NaturalModule

open PrimitiveAffineDegreeTwoTwelveRow17NaturalCoordinates

abbrev ActingRing := (ZMod 2)[Top]

/-- All invariant submodules of the two augmentation copies are cyclic,
with no enumeration or separate semisimplicity hypothesis. -/
theorem augmentation_uniform (W : Submodule ActingRing augmentation.asSubmodule) :
    ModuleGeneratedBy ActingRing W 1 := by
  let e : augmentation.asSubmodule ≃ₗ[ZMod 2] Rect :=
    augmentationChart.equiv.symm.trans rectangularCoordinates
  apply ModuleGeneratedBy.one_of_matrixUnits (by decide : 2 ≤ 4) e unitScalar
  intro i j x
  have hx : augmentationChart.inclusion (augmentationChart.coordinates x.1) = x.1 :=
    (augmentationChart.mem_iff _).mp x.property
  change rectangularCoordinates (augmentationChart.coordinates
      (representation.asAlgebraHom (unitScalar i j) x.1)) =
    Pi.single i (rectangularCoordinates (augmentationChart.coordinates x.1) j)
  rw [← unitOperator_eq]
  calc
    rectangularCoordinates (augmentationChart.coordinates (unitOperator i j x.1)) =
        rectangularCoordinates (augmentationChart.coordinates
          (unitOperator i j (augmentationChart.inclusion (augmentationChart.coordinates x.1)))) := by
      rw [hx]
    _ = rectangularCoordinates (rowUnit i j (augmentationChart.coordinates x.1)) := by
      rw [unit_apply, augmentationChart.left_inverse]
    _ = Pi.single i (rectangularCoordinates (augmentationChart.coordinates x.1) j) :=
      rectangularCoordinates.apply_symm_apply _

private theorem constants_polynomial_span :
    Submodule.span (ZMod 2)[X]
      (Set.range (fun _ : Fin 1 ↦ Module.AEval'.of (constants.toRepresentation s)
        (constantChart.equiv (Pi.single 0 1)))) = ⊤ := by
  let sigma := constants.toRepresentation
  let b : Fin 4 → constants.toSubmodule := fun i ↦ constantChart.equiv (Pi.single i 1)
  let e := Module.AEval'.of (sigma s)
  let code : Fin 1 → Module.AEval' (sigma s) := fun _ ↦ e (b 0)
  let P : Submodule (ZMod 2)[X] (Module.AEval' (sigma s)) :=
    Submodule.span (ZMod 2)[X] (Set.range code)
  have horbit (i : Fin 4) : sigma (s ^ i.val) (b 0) = b i := by
    apply Subtype.ext
    exact constant_orbit i
  have hb (i : Fin 4) : e (b i) ∈ P := by
    have hbase : e (b 0) ∈ P :=
      Submodule.subset_span ⟨0, rfl⟩
    have hpow := P.smul_mem ((Polynomial.X : (ZMod 2)[X]) ^ i.val) hbase
    have heq : ((Polynomial.X : (ZMod 2)[X]) ^ i.val) • e (b 0) =
        e (sigma (s ^ i.val) (b 0)) := by
      rw [Module.AEval'.X_pow_smul_of, map_pow]
      rfl
    rwa [heq, horbit] at hpow
  have hall (x : constants.toSubmodule) : e x ∈ P := by
    let v : Fin 4 → ZMod 2 := constantChart.equiv.symm x
    have hv : (∑ i : Fin 4, v i • (Pi.single i 1 : Fin 4 → ZMod 2)) = v := by
      ext j
      simp [Pi.single_apply, mul_ite]
    have hx : (∑ i : Fin 4, v i • b i) = x := by
      calc
        (∑ i : Fin 4, v i • b i) =
            constantChart.equiv (∑ i : Fin 4, v i • (Pi.single i 1)) := by
          simp only [map_sum, map_smul, b]
        _ = x := by
          rw [hv]
          exact constantChart.equiv.apply_symm_apply x
    have hm : (∑ i : Fin 4, v i • e (b i)) ∈ P :=
      P.sum_mem (fun i _ ↦ P.smul_of_tower_mem (v i) (hb i))
    have heq : (∑ i : Fin 4, v i • e (b i)) = e x := by
      simpa only [map_sum, map_smul] using congrArg e hx
    exact heq ▸ hm
  apply top_unique
  intro x _
  simpa only [LinearEquiv.apply_symm_apply] using hall (e.symm x)

theorem constants_uniform (W : Submodule ActingRing constants.asSubmodule) :
    ModuleGeneratedBy ActingRing W 1 := by
  have hrep : UniformSubrepresentationGeneratorBound constants.toRepresentation 1 :=
    uniformSubrepresentationGeneratorBound_of_polynomial constants.toRepresentation s _
      constants_polynomial_span
  have hmodule := (uniformSubrepresentationGeneratorBound_iff_submodule
    constants.toRepresentation 1).mp hrep
  exact ModuleGeneratedBy.uniform_congr (subrepresentationModuleEquiv constants) hmodule W

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
    _ = 0 := PrimitiveAffineDegreeTwoTwelveRow17NaturalCoordinates.projection_augmentation _

private theorem pieces_sup : constants.asSubmodule ⊔ augmentation.asSubmodule = ⊤ := by
  apply top_unique
  intro x _
  apply Submodule.mem_sup.mpr
  refine ⟨constantChart.inclusion (constantChart.coordinates x), ?_,
    augmentationChart.inclusion (augmentationChart.coordinates x), ?_, decomposition x⟩
  · exact ⟨constantChart.coordinates x, rfl⟩
  · exact ⟨augmentationChart.coordinates x, rfl⟩

/-- The exact original row-17 natural module has uniform generator bound
one, including submodules meeting both projected summands. -/
theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Top (Fin 12)) 1 := by
  apply (uniformSubrepresentationGeneratorBound_iff_submodule representation 1).mpr
  exact ModuleGeneratedBy.uniform_of_projected_submodules
    constants.asSubmodule augmentation.asSubmodule projectionScalar
    projection_constants projection_augmentation pieces_sup 1
    constants_uniform augmentation_uniform

end PrimitiveAffineDegreeTwoTwelveRow17NaturalModule
end SymmetricSubgroupAsymptotics

end
