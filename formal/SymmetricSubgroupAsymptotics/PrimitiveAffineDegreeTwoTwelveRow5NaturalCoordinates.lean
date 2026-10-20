import SymmetricSubgroupAsymptotics.BinaryCoordinateBasisChecks
import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry
import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import Mathlib.Algebra.Algebra.Tower

/-! Exact row5 coordinates and acting matrix units. The ternary average
splits four block constants from eight augmentation coordinates. On the
augmentation, a corrected reflection and the ternary translation give
two-by-two matrix units; the square of the original four-cycle acts on
each four-dimensional row as two transpositions. All certificates check
displayed basis vectors and retain the original three permutations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow5NaturalCoordinates

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev Top := Row5Top
abbrev Vector := Fin 12 → ZMod 2

def generators : Fin 3 → Top := closureGenerators row5Generators
theorem generators_full : Subgroup.closure (Set.range generators) = ⊤ :=
  closureGenerators_full row5Generators

def t : Top := generators 0
def s : Top := generators 2
def representation : Representation (ZMod 2) Top Vector :=
  permutationFunctionRepresentation (ZMod 2) Top (Fin 12)

def constantBasis : Fin 4 → ℕ := ![273, 546, 1092, 2184]
def augmentationBasis : Fin 8 → ℕ := ![2962, 1198, 3808, 2107, 697, 3658, 238, 2947]
def augmentationDual : Fin 8 → ℕ := ![427, 2758, 1768, 2587, 2737, 3178, 3718, 442]

def constantChart : BinaryCoordinateSpace 12 4 :=
  binaryCoordinateSpaceOfBasisMasks 12 4 constantBasis constantBasis (by
    intro i; funext j; revert i j; decide +kernel)

def augmentationChart : BinaryCoordinateSpace 12 8 :=
  binaryCoordinateSpaceOfBasisMasks 12 8 augmentationBasis augmentationDual (by
    intro i; funext j; revert i j; decide +kernel)

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

def rectangleIndex : Fin 2 × Fin 4 ≃ Fin 8 := finProdFinEquiv

def rectangularCoordinates :
    (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → Fin 4 → ZMod 2) where
  toFun v i j := v (rectangleIndex (i, j))
  invFun v q := v (rectangleIndex.symm q).1 (rectangleIndex.symm q).2
  left_inv v := by funext q; exact congrArg v (rectangleIndex.apply_symm_apply q)
  right_inv v := by
    funext i j
    change v (rectangleIndex.symm (rectangleIndex (i, j))).1
      (rectangleIndex.symm (rectangleIndex (i, j))).2 = v i j
    rw [rectangleIndex.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def constantOperator : Module.End (ZMod 2) (Fin 4 → ZMod 2) :=
  LinearMap.pi (fun i ↦ LinearMap.proj (![1, 2, 3, 0] i : Fin 4))

def fibreOperator : Module.End (ZMod 2) (Fin 4 → ZMod 2) :=
  LinearMap.pi (fun i ↦ LinearMap.proj (![1, 0, 3, 2] i : Fin 4))

def constantWitness : LiteralPolynomialSpanWitness constantOperator 1 3 where
  vectors _ m := Pi.single (![0, 3, 2, 1] m : Fin 4) 1
  step := by intro j m; funext x; revert j m x; decide +kernel
  selected i := (0, ![0, 3, 2, 1] i)
  coefficient i := Pi.single i 1
  point_eq := by decide +kernel

def fibreWitness : LiteralPolynomialSpanWitness fibreOperator 2 1 where
  vectors j m := Pi.single (![![0, 1], ![2, 3]] j m : Fin 4) 1
  step := by intro j m; funext x; revert j m x; decide +kernel
  selected := ![(0, 0), (0, 1), (1, 0), (1, 1)]
  coefficient i := Pi.single i 1
  point_eq := by decide +kernel

def matrixCoordinates (i j : Fin 2) : Module.End (ZMod 2) (Fin 8 → ZMod 2) :=
  rectangularCoordinates.symm.toLinearMap.comp
    ((LinearMap.single (ZMod 2) (fun _ : Fin 2 ↦ Fin 4 → ZMod 2) i).comp
      ((LinearMap.proj j).comp rectangularCoordinates.toLinearMap))

def fibreCoordinates : Module.End (ZMod 2) (Fin 8 → ZMod 2) :=
  rectangularCoordinates.symm.toLinearMap.comp
    (LinearMap.pi fun i : Fin 2 ↦ fibreOperator.comp
      ((LinearMap.proj i).comp rectangularCoordinates.toLinearMap))

def correctedReflectionOperator : Module.End (ZMod 2) Vector :=
  (1 + representation t * (1 + representation s ^ 2)) * representation s

def firstProjectionOperator : Module.End (ZMod 2) Vector :=
  (1 + correctedReflectionOperator) * representation t

def matrixOperator (i j : Fin 2) : Module.End (ZMod 2) Vector :=
  ![![firstProjectionOperator,
      firstProjectionOperator * representation t * (1 + firstProjectionOperator)],
    ![(1 + firstProjectionOperator) * representation t ^ 2 * firstProjectionOperator,
      1 + firstProjectionOperator]] i j

def correctedReflectionScalar : (ZMod 2)[Top] :=
  (1 + MonoidAlgebra.single t 1 * (1 + MonoidAlgebra.single s 1 ^ 2)) *
    MonoidAlgebra.single s 1

def firstProjectionScalar : (ZMod 2)[Top] :=
  (1 + correctedReflectionScalar) * MonoidAlgebra.single t 1

def matrixScalar (i j : Fin 2) : (ZMod 2)[Top] :=
  ![![firstProjectionScalar,
      firstProjectionScalar * MonoidAlgebra.single t 1 * (1 + firstProjectionScalar)],
    ![(1 + firstProjectionScalar) * MonoidAlgebra.single t 1 ^ 2 * firstProjectionScalar,
      1 + firstProjectionScalar]] i j

theorem matrixOperator_eq (i j : Fin 2) :
    matrixOperator i j = representation.asAlgebraHom (matrixScalar i j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [matrixOperator, matrixScalar, firstProjectionOperator, firstProjectionScalar,
      correctedReflectionOperator, correctedReflectionScalar, Matrix.cons_val_zero',
      Matrix.cons_val_succ', map_add, map_mul, map_pow, map_one,
      Representation.asAlgebraHom_single, one_smul]

private theorem constant_operator_basis : ∀ (j : Fin 4) (x : Fin 12),
    representation s (constantChart.inclusion (Pi.single j 1)) x =
      constantChart.inclusion (constantOperator (Pi.single j 1)) x := by decide +kernel

theorem constant_operator (v : Fin 4 → ZMod 2) :
    representation s (constantChart.inclusion v) = constantChart.inclusion (constantOperator v) := by
  have hm : (representation s).comp constantChart.inclusion =
      constantChart.inclusion.comp constantOperator := by
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro j
    rw [Pi.basisFun_apply]
    exact funext (constant_operator_basis j)
  exact LinearMap.congr_fun hm v

private theorem matrix_basis : ∀ (i j : Fin 2) (q : Fin 8) (x : Fin 12),
    matrixOperator i j (augmentationChart.inclusion (Pi.single q 1)) x =
      augmentationChart.inclusion (matrixCoordinates i j (Pi.single q 1)) x := by
  decide +kernel

theorem matrix_action (i j : Fin 2) (v : Fin 8 → ZMod 2) :
    matrixOperator i j (augmentationChart.inclusion v) =
      augmentationChart.inclusion (matrixCoordinates i j v) := by
  have hm : (matrixOperator i j).comp augmentationChart.inclusion =
      augmentationChart.inclusion.comp (matrixCoordinates i j) := by
    apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
    intro q
    rw [Pi.basisFun_apply]
    exact funext (matrix_basis i j q)
  exact LinearMap.congr_fun hm v

private theorem fibre_basis : ∀ (q : Fin 8) (x : Fin 12),
    (representation s ^ 2) (augmentationChart.inclusion (Pi.single q 1)) x =
      augmentationChart.inclusion (fibreCoordinates (Pi.single q 1)) x := by decide +kernel

theorem fibre_action (v : Fin 8 → ZMod 2) :
    (representation s ^ 2) (augmentationChart.inclusion v) =
      augmentationChart.inclusion (fibreCoordinates v) := by
  have hm : (representation s ^ 2).comp augmentationChart.inclusion =
      augmentationChart.inclusion.comp fibreCoordinates := by
    apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
    intro q
    rw [Pi.basisFun_apply]
    exact funext (fibre_basis q)
  exact LinearMap.congr_fun hm v

def projectionOperator : Module.End (ZMod 2) Vector :=
  1 + representation t + representation t ^ 2

def projectionScalar : (ZMod 2)[Top] :=
  1 + MonoidAlgebra.single t 1 + MonoidAlgebra.single t 1 ^ 2

theorem projectionOperator_eq : projectionOperator = representation.asAlgebraHom projectionScalar := by
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

end PrimitiveAffineDegreeTwoTwelveRow5NaturalCoordinates
end SymmetricSubgroupAsymptotics

end
