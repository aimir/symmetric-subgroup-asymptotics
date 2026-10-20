import SymmetricSubgroupAsymptotics.BinaryCoordinateBasisChecks
import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry
import SymmetricSubgroupAsymptotics.BinaryLocalAlternatingFourPolynomial
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import Mathlib.Algebra.Algebra.Tower

/-! Exact coordinates for the augmentation-translation/A4 root action.
The original generators are t=(1,1,1,0), s=(012), a=(123), on four
centered ternary blocks. Two ternary norms separate block constants from
augmentation, and their difference isolates the last augmentation fibre.
Pure block permutations transport this fibre to give actual matrix units.
All finite certificates test displayed basis vectors only. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow133NaturalCoordinates

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev Top := Row133Top
abbrev Vector := Fin 12 → ZMod 2

def generators : Fin 3 → Top := closureGenerators row133Generators
theorem generators_full : Subgroup.closure (Set.range generators) = ⊤ :=
  closureGenerators_full row133Generators

def t : Top := generators 0
def s : Top := generators 1
def a : Top := generators 2
def u : Top := a * t * a⁻¹
def d : Top := a ^ 2 * s * a ^ 2
def transport : Fin 4 → Top := ![s ^ 2 * a, a, s * a, 1]

def representation : Representation (ZMod 2) Top Vector :=
  permutationFunctionRepresentation (ZMod 2) Top (Fin 12)

def constantBasis : Fin 4 → ℕ := ![2184, 1092, 546, 273]
def augmentationBasis : Fin 8 → ℕ := ![2176, 136, 1028, 1088, 34, 514, 272, 17]
def augmentationDual : Fin 8 → ℕ := ![136, 2176, 1088, 1028, 514, 34, 17, 272]

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

def rectangleIndex : Fin 4 × Fin 2 ≃ Fin 8 := finProdFinEquiv

def rectangularCoordinates :
    (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → Fin 2 → ZMod 2) where
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

def matrixCoordinates (i j : Fin 4) : Module.End (ZMod 2) (Fin 8 → ZMod 2) :=
  rectangularCoordinates.symm.toLinearMap.comp
    ((LinearMap.single (ZMod 2) (fun _ : Fin 4 ↦ Fin 2 → ZMod 2) i).comp
      ((LinearMap.proj j).comp rectangularCoordinates.toLinearMap))

def normOperator (g : Top) : Module.End (ZMod 2) Vector :=
  1 + representation g + representation g ^ 2

def normScalar (g : Top) : (ZMod 2)[Top] :=
  1 + MonoidAlgebra.single g 1 + MonoidAlgebra.single g 1 ^ 2

theorem normOperator_eq (g : Top) :
    normOperator g = representation.asAlgebraHom (normScalar g) := by
  simp only [normOperator, normScalar, map_add, map_pow, map_one,
    Representation.asAlgebraHom_single, one_smul]

def constantOperator : Module.End (ZMod 2) (Fin 4 → ZMod 2) :=
  BinaryLocalAlternatingFourPolynomial.operator (ZMod 2)

def constantActionOperator : Module.End (ZMod 2) Vector :=
  normOperator a * representation d * normOperator a + 1 + representation a ^ 2

def constantActionScalar : (ZMod 2)[Top] :=
  normScalar a * MonoidAlgebra.single d 1 * normScalar a + 1 +
    MonoidAlgebra.single a 1 ^ 2

theorem constantActionOperator_eq :
    constantActionOperator = representation.asAlgebraHom constantActionScalar := by
  simp only [constantActionOperator, constantActionScalar, map_mul, map_add, map_pow,
    map_one, Representation.asAlgebraHom_single, one_smul, ← normOperator_eq]

def matrixOperator (i j : Fin 4) : Module.End (ZMod 2) Vector :=
  representation (transport i) * (normOperator t * (1 + normOperator u)) *
    representation (transport j)⁻¹

def matrixScalar (i j : Fin 4) : (ZMod 2)[Top] :=
  MonoidAlgebra.single (transport i) 1 * (normScalar t * (1 + normScalar u)) *
    MonoidAlgebra.single (transport j)⁻¹ 1

theorem matrixOperator_eq (i j : Fin 4) :
    matrixOperator i j = representation.asAlgebraHom (matrixScalar i j) := by
  simp only [matrixOperator, matrixScalar, map_mul, map_add, map_one,
    Representation.asAlgebraHom_single, one_smul, ← normOperator_eq]

private theorem constant_operator_basis : ∀ (j : Fin 4) (x : Fin 12),
    constantActionOperator (constantChart.inclusion (Pi.single j 1)) x =
      constantChart.inclusion (constantOperator (Pi.single j 1)) x := by
  decide +kernel

theorem constant_operator (v : Fin 4 → ZMod 2) :
    constantActionOperator (constantChart.inclusion v) =
      constantChart.inclusion (constantOperator v) := by
  have hm : constantActionOperator.comp constantChart.inclusion =
      constantChart.inclusion.comp constantOperator := by
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro j
    rw [Pi.basisFun_apply]
    exact funext (constant_operator_basis j)
  exact LinearMap.congr_fun hm v

private theorem matrix_basis : ∀ (i j : Fin 4) (q : Fin 8) (x : Fin 12),
    matrixOperator i j (augmentationChart.inclusion (Pi.single q 1)) x =
      augmentationChart.inclusion (matrixCoordinates i j (Pi.single q 1)) x := by
  decide +kernel

theorem matrix_action (i j : Fin 4) (v : Fin 8 → ZMod 2) :
    matrixOperator i j (augmentationChart.inclusion v) =
      augmentationChart.inclusion (matrixCoordinates i j v) := by
  have hm : (matrixOperator i j).comp augmentationChart.inclusion =
      augmentationChart.inclusion.comp (matrixCoordinates i j) := by
    apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
    intro q
    rw [Pi.basisFun_apply]
    exact funext (matrix_basis i j q)
  exact LinearMap.congr_fun hm v

def projectionOperator : Module.End (ZMod 2) Vector := normOperator t * normOperator u
def projectionScalar : (ZMod 2)[Top] := normScalar t * normScalar u

theorem projectionOperator_eq : projectionOperator = representation.asAlgebraHom projectionScalar := by
  simp only [projectionOperator, projectionScalar, map_mul, ← normOperator_eq]

private theorem projection_constant_basis : ∀ (j : Fin 4) (x : Fin 12),
    projectionOperator (constantChart.inclusion (Pi.single j 1)) x =
      constantChart.inclusion (Pi.single j 1) x := by decide +kernel

private theorem projection_augmentation_basis : ∀ (j : Fin 8) (x : Fin 12),
    projectionOperator (augmentationChart.inclusion (Pi.single j 1)) x = 0 := by
  decide +kernel

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

end PrimitiveAffineDegreeTwoTwelveRow133NaturalCoordinates
end SymmetricSubgroupAsymptotics

end
