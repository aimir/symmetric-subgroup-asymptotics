import SymmetricSubgroupAsymptotics.BinaryFourCanonicalLocalMiddleInclusion
import SymmetricSubgroupAsymptotics.BinaryFourAmbientBottom

/-! Exact bottom and augmentation maps of the actual S4 frame. Both
local planes use the retained local action, including odd reflection. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourFullBlockCoordinates BinaryFourSymmetricBlockActions

def bottomCoordinatesLinear : Local →ₗ[Scalar] FullCoordinates where
  toFun a := ![a 0, a 1, 0, 0, 0, 0, 0, 0]
  map_add' := by intro x y; ext i; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i; fin_cases i <;> rfl

def bottomProjectionLinear : FullCoordinates →ₗ[Scalar] Local where
  toFun x := ![x 0, x 1]
  map_add' := by intro x y; ext i; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i; fin_cases i <;> rfl

def fullAugmentationLinear : FullCoordinates →ₗ[Scalar] Local where
  toFun := augmentation
  map_add' := by intro x y; ext i; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i; fin_cases i <;> rfl

def canonicalBottomIntertwiner : canonicalLocalRepresentation.IntertwiningMap
    BinaryFourCanonicalSymmetricInducedChart.fullCoordinatesRepresentation where
  toLinearMap := bottomCoordinatesLinear
  isIntertwining' g := by
    apply (Pi.basisFun Scalar (Fin 2)).ext
    intro i
    rw [Pi.basisFun_apply]
    rcases g with ⟨⟨p, z⟩, b⟩
    revert p z b i
    decide +kernel

def canonicalAugmentationIntertwiner :
    BinaryFourCanonicalSymmetricInducedChart.fullCoordinatesRepresentation.IntertwiningMap
      canonicalLocalRepresentation where
  toLinearMap := fullAugmentationLinear
  isIntertwining' g := by
    apply (Pi.basisFun Scalar (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rcases g with ⟨⟨p, z⟩, b⟩
    revert p z b i
    decide +kernel

theorem bottomProjection_coordinates (a : Local) :
    bottomProjectionLinear (bottomCoordinatesLinear a) = a := by
  ext i
  fin_cases i <;> rfl

theorem bottom_coordinates_of_diagonal (x : FullCoordinates)
    (hx : ∃ a : Local, fullChart x = diagonal a) :
    bottomCoordinatesLinear (bottomProjectionLinear x) = x := by
  obtain ⟨a, ha⟩ := hx
  have identity : ∀ (x : FullCoordinates) (a : Local), fullChart x = diagonal a →
      bottomCoordinatesLinear (bottomProjectionLinear x) = x := by decide +kernel
  exact identity x a ha

theorem bottomProjection_action (g : SymmetricComplement) (x : FullCoordinates)
    (hx : ∃ a : Local, fullChart x = diagonal a) :
    bottomProjectionLinear
      (BinaryFourCanonicalSymmetricInducedChart.fullCoordinatesRepresentation g x) =
      canonicalLocalRepresentation g (bottomProjectionLinear x) := by
  have h := Representation.IntertwiningMap.isIntertwining _ _ canonicalBottomIntertwiner
    g (bottomProjectionLinear x)
  have hproj := congrArg bottomProjectionLinear h
  change bottomProjectionLinear
      (bottomCoordinatesLinear (canonicalLocalRepresentation g (bottomProjectionLinear x))) =
    bottomProjectionLinear
      (BinaryFourCanonicalSymmetricInducedChart.fullCoordinatesRepresentation g
        (bottomCoordinatesLinear (bottomProjectionLinear x))) at hproj
  rw [bottom_coordinates_of_diagonal x hx, bottomProjection_coordinates] at hproj
  exact hproj.symm

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
