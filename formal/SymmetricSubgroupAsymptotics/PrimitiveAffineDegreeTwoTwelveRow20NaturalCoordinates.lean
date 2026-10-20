import SymmetricSubgroupAsymptotics.BinaryCoordinateBasisChecks
import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry
import SymmetricSubgroupAsymptotics.BinaryLocalAlternatingFourPolynomial
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import Mathlib.Algebra.Algebra.Tower

/-! Exact row20 coordinates. The chart (u,v) ↦ 3u+4v modulo12 makes
the first two generators act on four positions and the third on three
positions. The central ternary projector separates four constant and
eight augmentation coordinates. All certificates check basis vectors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow20NaturalCoordinates

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev Top := Row20Top
abbrev Vector := Fin 12 → ZMod 2
abbrev Scalar := BinaryQuadraticField.Scalar

def generators : Fin 3 → Top := closureGenerators row20Generators
theorem generators_full : Subgroup.closure (Set.range generators) = ⊤ :=
  closureGenerators_full row20Generators

def a : Top := generators 0
def b : Top := generators 1
def c : Top := generators 2
def representation : Representation (ZMod 2) Top Vector :=
  permutationFunctionRepresentation (ZMod 2) Top (Fin 12)

def constantBasis : Fin 4 → ℕ := ![273, 2184, 1092, 546]
def augmentationBasis : Fin 8 → ℕ := ![257, 272, 2056, 2176, 68, 1028, 544, 34]
def augmentationDual : Fin 8 → ℕ := ![272, 257, 2176, 2056, 1028, 68, 34, 544]

def constantChart : BinaryCoordinateSpace 12 4 :=
  binaryCoordinateSpaceOfBasisMasks 12 4 constantBasis constantBasis (by
    intro i
    funext j
    revert i j
    decide +kernel)

def augmentationChart : BinaryCoordinateSpace 12 8 :=
  binaryCoordinateSpaceOfBasisMasks 12 8 augmentationBasis augmentationDual (by
    intro i
    funext j
    revert i j
    decide +kernel)

private theorem constant_positive : ∀ q j x,
    constantChart.inclusion (constantChart.coordinates
      (representation (generators q) (constantChart.inclusion (Pi.single j 1)))) x =
      representation (generators q) (constantChart.inclusion (Pi.single j 1)) x := by
  decide +kernel

private theorem constant_negative : ∀ q j x,
    constantChart.inclusion (constantChart.coordinates
      (representation (generators q)⁻¹ (constantChart.inclusion (Pi.single j 1)))) x =
      representation (generators q)⁻¹ (constantChart.inclusion (Pi.single j 1)) x := by
  decide +kernel

private theorem augmentation_positive : ∀ q j x,
    augmentationChart.inclusion (augmentationChart.coordinates
      (representation (generators q) (augmentationChart.inclusion (Pi.single j 1)))) x =
      representation (generators q) (augmentationChart.inclusion (Pi.single j 1)) x := by
  decide +kernel

private theorem augmentation_negative : ∀ q j x,
    augmentationChart.inclusion (augmentationChart.coordinates
      (representation (generators q)⁻¹ (augmentationChart.inclusion (Pi.single j 1)))) x =
      representation (generators q)⁻¹ (augmentationChart.inclusion (Pi.single j 1)) x := by
  decide +kernel

def constants : Subrepresentation representation :=
  constantChart.subrepresentationOfGenerators representation generators generators_full
    (fun q j ↦ (constantChart.mem_iff _).mpr (funext (constant_positive q j)))
    (fun q j ↦ (constantChart.mem_iff _).mpr (funext (constant_negative q j)))

def augmentation : Subrepresentation representation :=
  augmentationChart.subrepresentationOfGenerators representation generators generators_full
    (fun q j ↦ (augmentationChart.mem_iff _).mpr (funext (augmentation_positive q j)))
    (fun q j ↦ (augmentationChart.mem_iff _).mpr (funext (augmentation_negative q j)))

def rectangleIndex : Fin 4 × Fin 2 ≃ Fin 8 := finProdFinEquiv

def rectangularCoordinates :
    (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → Fin 2 → ZMod 2) where
  toFun v i j := v (rectangleIndex (i, j))
  invFun v t := v (rectangleIndex.symm t).1 (rectangleIndex.symm t).2
  left_inv v := by
    funext t
    exact congrArg v (rectangleIndex.apply_symm_apply t)
  right_inv v := by
    funext i j
    change v (rectangleIndex.symm (rectangleIndex (i, j))).1
      (rectangleIndex.symm (rectangleIndex (i, j))).2 = v i j
    rw [rectangleIndex.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fieldCoordinates : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → Scalar) :=
  rectangularCoordinates.trans (LinearEquiv.piCongrRight fun _ : Fin 4 ↦
    (QuadraticAlgebra.linearEquivTuple (1 : ZMod 2) 1).symm)

def coordinateOperator : Module.End (ZMod 2) (Fin 8 → ZMod 2) :=
  fieldCoordinates.symm.toLinearMap.comp
    (((BinaryLocalAlternatingFourPolynomial.operator Scalar).restrictScalars (ZMod 2)).comp
      fieldCoordinates.toLinearMap)

def omegaOperator : Module.End (ZMod 2) (Fin 8 → ZMod 2) :=
  fieldCoordinates.symm.toLinearMap.comp
    ((Algebra.lsmul (ZMod 2) (ZMod 2) (Fin 4 → Scalar) BinaryQuadraticField.omega).comp
      fieldCoordinates.toLinearMap)

def averageOperator : Module.End (ZMod 2) Vector :=
  1 + representation a + representation a ^ 2

def operator : Module.End (ZMod 2) Vector :=
  averageOperator * representation (a * b) * averageOperator + 1 + representation a ^ 2

def averageScalar : (ZMod 2)[Top] :=
  1 + MonoidAlgebra.single a 1 + MonoidAlgebra.single a 1 ^ 2

def operatorScalar : (ZMod 2)[Top] :=
  averageScalar * MonoidAlgebra.single (a * b) 1 * averageScalar + 1 +
    MonoidAlgebra.single a 1 ^ 2

theorem operator_eq : operator = representation.asAlgebraHom operatorScalar := by
  simp only [operator, averageOperator, operatorScalar, averageScalar, map_mul, map_add,
    map_pow, map_one, Representation.asAlgebraHom_single, one_smul]

private theorem constant_operator_basis : ∀ (j : Fin 4) (x : Fin 12),
    operator (constantChart.inclusion (Pi.single j 1)) x =
      constantChart.inclusion
        (BinaryLocalAlternatingFourPolynomial.operator (ZMod 2) (Pi.single j 1)) x := by
  decide +kernel

private theorem augmentation_operator_basis : ∀ (j : Fin 8) (x : Fin 12),
    operator (augmentationChart.inclusion (Pi.single j 1)) x =
      augmentationChart.inclusion (coordinateOperator (Pi.single j 1)) x := by
  decide +kernel

private theorem omega_basis : ∀ (j : Fin 8) (x : Fin 12),
    representation c⁻¹ (augmentationChart.inclusion (Pi.single j 1)) x =
      augmentationChart.inclusion (omegaOperator (Pi.single j 1)) x := by
  decide +kernel

theorem constant_operator (v : Fin 4 → ZMod 2) :
    operator (constantChart.inclusion v) = constantChart.inclusion
      (BinaryLocalAlternatingFourPolynomial.operator (ZMod 2) v) := by
  have hm : operator.comp constantChart.inclusion = constantChart.inclusion.comp
      (BinaryLocalAlternatingFourPolynomial.operator (ZMod 2)) := by
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro j
    rw [Pi.basisFun_apply]
    exact funext (constant_operator_basis j)
  exact LinearMap.congr_fun hm v

theorem augmentation_operator (v : Fin 8 → ZMod 2) :
    operator (augmentationChart.inclusion v) =
      augmentationChart.inclusion (coordinateOperator v) := by
  have hm : operator.comp augmentationChart.inclusion =
      augmentationChart.inclusion.comp coordinateOperator := by
    apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
    intro j
    rw [Pi.basisFun_apply]
    exact funext (augmentation_operator_basis j)
  exact LinearMap.congr_fun hm v

theorem omega_apply (v : Fin 8 → ZMod 2) :
    representation c⁻¹ (augmentationChart.inclusion v) =
      augmentationChart.inclusion (omegaOperator v) := by
  have hm : (representation c⁻¹).comp augmentationChart.inclusion =
      augmentationChart.inclusion.comp omegaOperator := by
    apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
    intro j
    rw [Pi.basisFun_apply]
    exact funext (omega_basis j)
  exact LinearMap.congr_fun hm v

def projectionOperator : Module.End (ZMod 2) Vector :=
  1 + representation c + representation c ^ 2

def projectionScalar : (ZMod 2)[Top] :=
  1 + MonoidAlgebra.single c 1 + MonoidAlgebra.single c 1 ^ 2

theorem projectionOperator_eq :
    projectionOperator = representation.asAlgebraHom projectionScalar := by
  simp only [projectionOperator, projectionScalar, map_add, map_pow, map_one,
    Representation.asAlgebraHom_single, one_smul]

private theorem projection_constant_basis : ∀ (j : Fin 4) (x : Fin 12),
    projectionOperator (constantChart.inclusion (Pi.single j 1)) x =
      constantChart.inclusion (Pi.single j 1) x := by decide +kernel

private theorem projection_augmentation_basis : ∀ (j : Fin 8) (x : Fin 12),
    projectionOperator (augmentationChart.inclusion (Pi.single j 1)) x = 0 := by decide +kernel

theorem projection_constant (v : Fin 4 → ZMod 2) :
    projectionOperator (constantChart.inclusion v) = constantChart.inclusion v := by
  have hm : projectionOperator.comp constantChart.inclusion = constantChart.inclusion := by
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro j
    rw [Pi.basisFun_apply]
    exact funext (projection_constant_basis j)
  exact LinearMap.congr_fun hm v

theorem projection_augmentation (v : Fin 8 → ZMod 2) :
    projectionOperator (augmentationChart.inclusion v) = 0 := by
  have hm : projectionOperator.comp augmentationChart.inclusion = 0 := by
    apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
    intro j
    rw [Pi.basisFun_apply]
    exact funext (projection_augmentation_basis j)
  exact LinearMap.congr_fun hm v

private theorem decomposition_basis : ∀ (i x : Fin 12),
    (constantChart.inclusion.comp constantChart.coordinates +
      augmentationChart.inclusion.comp augmentationChart.coordinates)
        (Pi.single i 1) x = (Pi.single i 1 : Vector) x := by decide +kernel

theorem decomposition (v : Vector) :
    constantChart.inclusion (constantChart.coordinates v) +
      augmentationChart.inclusion (augmentationChart.coordinates v) = v := by
  have hm : constantChart.inclusion.comp constantChart.coordinates +
      augmentationChart.inclusion.comp augmentationChart.coordinates = LinearMap.id := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact funext (decomposition_basis i)
  exact LinearMap.congr_fun hm v

end PrimitiveAffineDegreeTwoTwelveRow20NaturalCoordinates
end SymmetricSubgroupAsymptotics

end
