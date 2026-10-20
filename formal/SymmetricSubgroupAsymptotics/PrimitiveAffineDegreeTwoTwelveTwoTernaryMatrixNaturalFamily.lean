import SymmetricSubgroupAsymptotics.BinaryTwoTernaryMatrixCoordinates
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Two more original joint natural fields share the checked two-ternary
matrix-block formula. Their literal sparse coordinates differ from the
row201 pilot, while their fibre operators and four matrix rows are common.
Both exports retain the historical natural capacity one. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryMatrixNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue BinaryTwoTernaryMatrixBlocks

/-- Original row237, zero-based index236, joint; historical natural1. -/
def row237BasisMask : Fin 12 → ℕ := ![546, 2312, 1092, 145, 34, 68, 514, 1028, 2056, 17, 264, 144]
def row237DualMask : Fin 12 → ℕ := ![546, 2312, 1092, 145, 514, 1028, 34, 68, 264, 144, 2056, 17]

def row237FullCoordinates : Vector ≃ₗ[ZMod 2] Vector where
  toFun := binaryMaskCoordinates 12 12 row237DualMask
  invFun := binaryMaskInclusion 12 12 row237BasisMask
  left_inv x := by
    have h : (binaryMaskInclusion 12 12 row237BasisMask).comp
        (binaryMaskCoordinates 12 12 row237DualMask) = LinearMap.id := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro i
      rw [Pi.basisFun_apply]
      funext j
      revert i j
      decide +kernel
    exact LinearMap.congr_fun h x
  right_inv x := by
    have h : (binaryMaskCoordinates 12 12 row237DualMask).comp
        (binaryMaskInclusion 12 12 row237BasisMask) = LinearMap.id := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro i
      rw [Pi.basisFun_apply]
      funext j
      revert i j
      decide +kernel
    exact LinearMap.congr_fun h x
  map_add' := (binaryMaskCoordinates 12 12 row237DualMask).map_add
  map_smul' := (binaryMaskCoordinates 12 12 row237DualMask).map_smul

def row237Coordinates : Vector ≃ₗ[ZMod 2] Blocks :=
  row237FullCoordinates.trans splitCoordinates

def row237Rotation : Row237Top := closureGenerators row237Generators 1
def row237Exchange : Row237Top := closureGenerators row237Generators 3
def row237Reflection : Row237Top := row237Exchange * closureGenerators row237Generators 2 * row237Exchange⁻¹

theorem row237Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row237Interface.top (Fin 12)) 1 := by
  apply uniform_of_coordinates row237Coordinates _ row237Rotation row237Exchange row237Reflection
  · intro i
    fin_cases i <;> intro r t <;> fin_cases r <;> fin_cases t <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

/-- Original row238, zero-based index237, joint; historical natural1. -/
def row238BasisMask : Fin 12 → ℕ := ![546, 273, 1092, 2184, 34, 68, 514, 1028, 2176, 257, 2056, 17]
def row238DualMask : Fin 12 → ℕ := ![546, 273, 1092, 2184, 514, 1028, 34, 68, 2056, 17, 2176, 257]

def row238FullCoordinates : Vector ≃ₗ[ZMod 2] Vector where
  toFun := binaryMaskCoordinates 12 12 row238DualMask
  invFun := binaryMaskInclusion 12 12 row238BasisMask
  left_inv x := by
    have h : (binaryMaskInclusion 12 12 row238BasisMask).comp
        (binaryMaskCoordinates 12 12 row238DualMask) = LinearMap.id := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro i
      rw [Pi.basisFun_apply]
      funext j
      revert i j
      decide +kernel
    exact LinearMap.congr_fun h x
  right_inv x := by
    have h : (binaryMaskCoordinates 12 12 row238DualMask).comp
        (binaryMaskInclusion 12 12 row238BasisMask) = LinearMap.id := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro i
      rw [Pi.basisFun_apply]
      funext j
      revert i j
      decide +kernel
    exact LinearMap.congr_fun h x
  map_add' := (binaryMaskCoordinates 12 12 row238DualMask).map_add
  map_smul' := (binaryMaskCoordinates 12 12 row238DualMask).map_smul

def row238Coordinates : Vector ≃ₗ[ZMod 2] Blocks :=
  row238FullCoordinates.trans splitCoordinates

def row238Rotation : Row238Top := closureGenerators row238Generators 1
def row238Exchange : Row238Top := closureGenerators row238Generators 2
def row238Reflection : Row238Top := closureGenerators row238Generators 3

theorem row238Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row238Interface.top (Fin 12)) 1 := by
  apply uniform_of_coordinates row238Coordinates _ row238Rotation row238Exchange row238Reflection
  · intro i
    fin_cases i <;> intro r t <;> fin_cases r <;> fin_cases t <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryMatrixNaturalFamily

end
