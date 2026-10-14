import SymmetricSubgroupAsymptotics.BinaryFourAugmentationActions

/-! Full eight-dimensional coordinates extending the checked six-dimensional
augmentation chart. The last two coordinates are the actual block sum.
The three linear maps below are the pure block actions in the same gauge. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation

abbrev FullCoordinates := Fin 8 → Scalar

def head (x : FullCoordinates) : Coordinates :=
  ![x 0, x 1, x 2, x 3, x 4, x 5]

def augmentation (x : FullCoordinates) : Local := ![x 6, x 7]

def includeAugmentation (x : Coordinates) : FullCoordinates :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, 0, 0]

def fullDecode (x : FullCoordinates) : BinaryFourBlockAugmentation.Module :=
  ![![x 0 + x 3 + x 4 + x 6, x 1 + x 2 + x 4 + x 7],
    ![x 0, x 1 + x 2],
    ![x 0 + x 3 + x 5, x 1 + x 5],
    ![x 0 + x 4 + x 5, x 1 + x 4 + x 5]]

def fullEncode (w : BinaryFourBlockAugmentation.Module) : FullCoordinates :=
  ![w 1 0,
    w 1 0 + w 3 0 + w 3 1,
    w 1 1 + w 1 0 + w 3 0 + w 3 1,
    w 2 0 + w 2 1 + w 3 0 + w 3 1,
    w 3 1 + w 2 1,
    w 2 1 + w 1 0 + w 3 0 + w 3 1,
    w 0 0 + w 1 0 + w 2 0 + w 3 0,
    w 0 1 + w 1 1 + w 2 1 + w 3 1]

theorem fullEncode_fullDecode (x : FullCoordinates) :
    fullEncode (fullDecode x) = x := by
  ext i
  fin_cases i <;> simp [fullEncode, fullDecode] <;> ring_nf <;>
    simp only [show (2 : Scalar) = 0 from by decide +kernel,
      show (3 : Scalar) = 1 from by decide +kernel,
      show (4 : Scalar) = 0 from by decide +kernel,
      mul_zero, mul_one, zero_add, add_zero]

theorem fullDecode_fullEncode (w : BinaryFourBlockAugmentation.Module) :
    fullDecode (fullEncode w) = w := by
  ext b i
  fin_cases b <;> fin_cases i <;> simp [fullEncode, fullDecode] <;> ring_nf <;>
    simp only [show (2 : Scalar) = 0 from by decide +kernel,
      show (3 : Scalar) = 1 from by decide +kernel,
      show (4 : Scalar) = 0 from by decide +kernel,
      mul_zero, mul_one, zero_add, add_zero]

def fullChart : FullCoordinates ≃ₗ[Scalar] BinaryFourBlockAugmentation.Module where
  toFun := fullDecode
  invFun := fullEncode
  left_inv := fullEncode_fullDecode
  right_inv := fullDecode_fullEncode
  map_add' := by
    intro x y
    ext b i
    fin_cases b <;> fin_cases i <;> simp [fullDecode] <;> ring
  map_smul' := by
    intro a x
    ext b i
    fin_cases b <;> fin_cases i <;> simp [fullDecode] <;> ring

theorem fullDecode_include (x : Coordinates) : fullDecode (includeAugmentation x) = decode x := by
  ext b i
  fin_cases b <;> fin_cases i <;> simp [fullDecode, includeAugmentation, decode]

theorem fullDecode_augmentation (x : FullCoordinates) :
    fullDecode x 0 + fullDecode x 1 + fullDecode x 2 + fullDecode x 3 =
      augmentation x := by
  ext i
  fin_cases i <;> simp [fullDecode, augmentation] <;> ring_nf <;>
    simp only [show (2 : Scalar) = 0 from by decide +kernel,
      show (4 : Scalar) = 0 from by decide +kernel,
      mul_zero, zero_add, add_zero]

def fullU : FullCoordinates ≃ₗ[Scalar] FullCoordinates where
  toFun x := ![x 0 + x 4 + x 5, x 1 + x 2 + x 4 + x 5,
    x 2, x 3 + x 6 + x 7, x 4 + x 7, x 5 + x 7, x 6, x 7]
  invFun x := ![x 0 + x 4 + x 5, x 1 + x 2 + x 4 + x 5,
    x 2, x 3 + x 6 + x 7, x 4 + x 7, x 5 + x 7, x 6, x 7]
  left_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel,
        mul_zero, zero_add, add_zero]
  right_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel,
        mul_zero, zero_add, add_zero]
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro a x; ext i; fin_cases i <;> simp <;> ring

def fullV : FullCoordinates ≃ₗ[Scalar] FullCoordinates where
  toFun x := ![x 0 + x 3 + x 4 + x 6, x 1 + x 4 + x 6,
    x 2 + x 6 + x 7, x 3, x 4, x 5 + x 6, x 6, x 7]
  invFun x := ![x 0 + x 3 + x 4 + x 6, x 1 + x 4 + x 6,
    x 2 + x 6 + x 7, x 3, x 4, x 5 + x 6, x 6, x 7]
  left_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel,
        mul_zero, zero_add, add_zero]
  right_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel,
        mul_zero, zero_add, add_zero]
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro a x; ext i; fin_cases i <;> simp <;> ring

def fullC : FullCoordinates ≃ₗ[Scalar] FullCoordinates where
  toFun x := ![x 0 + x 1, x 0 + x 5, x 4, x 2 + x 5, x 3 + x 5,
    x 5, x 6 + x 7, x 6]
  invFun x := ![x 1 + x 5, x 0 + x 1 + x 5, x 3 + x 5, x 4 + x 5,
    x 2, x 5, x 7, x 6 + x 7]
  left_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel,
        mul_zero, zero_add, add_zero]
  right_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel,
        mul_zero, zero_add, add_zero]
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro a x; ext i; fin_cases i <;> simp <;> ring

theorem fullU_include (x : Coordinates) : fullU (includeAugmentation x) = includeAugmentation (u x) := by
  ext i; fin_cases i <;> simp [fullU, includeAugmentation, u]

theorem fullV_include (x : Coordinates) : fullV (includeAugmentation x) = includeAugmentation (v x) := by
  ext i; fin_cases i <;> simp [fullV, includeAugmentation, v]

theorem fullC_include (x : Coordinates) : fullC (includeAugmentation x) = includeAugmentation (c x) := by
  ext i; fin_cases i <;> simp [fullC, includeAugmentation, c]

theorem fullU_square : fullU ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro x
  change fullU (fullU x) = x
  exact fullU.left_inv x

theorem fullV_square : fullV ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro x
  change fullV (fullV x) = x
  exact fullV.left_inv x

theorem fullC_cube : fullC ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [pow_succ, fullC] <;> ring_nf <;>
    simp only [show (2 : Scalar) = 0 from by decide +kernel,
      show (3 : Scalar) = 1 from by decide +kernel,
      show (4 : Scalar) = 0 from by decide +kernel,
      mul_zero, mul_one, zero_add, add_zero]

/-- Only eight displayed basis vectors are needed to compare linear maps. -/
theorem linearEquiv_ext_basis {f g : FullCoordinates ≃ₗ[Scalar] FullCoordinates}
    (h : ∀ i : Fin 8, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  have hl : f.toLinearMap = g.toLinearMap := by
    apply (Pi.basisFun Scalar (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact h i
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun hl x

theorem fullU_fullV_commute : Commute fullU fullV := by
  change fullU * fullV = fullV * fullU
  apply linearEquiv_ext_basis
  intro i
  revert i
  decide +kernel

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
