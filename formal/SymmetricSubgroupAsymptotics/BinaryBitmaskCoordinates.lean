import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Executable binary bit-mask coordinates

Selected finite certificates store vectors and matrix columns as natural
number bit masks.  These definitions turn those masks into literal
`ZMod 2` vectors, matrices and reversible coordinate charts.  Generated
files still prove every inverse equation with the Lean kernel.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Decode the low `w` bits of a natural number as a binary vector. -/
def binaryVectorOfMask (w : ℕ) (mask : ℕ) : Fin w → ZMod 2 :=
  fun i ↦ if mask.testBit i then 1 else 0

/-- The executable natural-number code of a binary vector. -/
def binaryVectorMask {w : ℕ} (v : Fin w → ZMod 2) : ℕ :=
  ∑ i, (v i).val * 2 ^ i.val

/-- A binary matrix specified by its natural-number column masks. -/
def binaryMatrixOfColumnMasks (d : ℕ) (columns : Fin d → ℕ) :
    Matrix (Fin d) (Fin d) (ZMod 2) :=
  fun i j ↦ if (columns j).testBit i then 1 else 0

/-- A rectangular binary matrix specified by column masks. -/
def binaryRectangularMatrixOfColumnMasks (w d : ℕ)
    (columns : Fin d → ℕ) : Matrix (Fin w) (Fin d) (ZMod 2) :=
  fun i j ↦ if (columns j).testBit i then 1 else 0

/-- Dot product with one stored binary mask. -/
def binaryMaskCoordinate {w : ℕ} (mask : ℕ)
    (v : Fin w → ZMod 2) : ZMod 2 :=
  ∑ i : Fin w, (if mask.testBit i.val then v i else 0)

/-- Build a reversible coordinate space from basis and dual bit masks.
The only premise is the literal left-inverse equation. -/
def binaryCoordinateSpaceOfMasks (w d : ℕ)
    (basis dual : Fin d → ℕ)
    (left_inverse : ∀ v : Fin d → ZMod 2,
      (fun j ↦ binaryMaskCoordinate (dual j)
        ((binaryRectangularMatrixOfColumnMasks w d basis).mulVec v)) = v) :
    BinaryCoordinateSpace w d where
  inclusion :=
    (binaryRectangularMatrixOfColumnMasks w d basis).mulVecLin
  coordinates := {
    toFun := fun v j ↦ binaryMaskCoordinate (dual j) v
    map_add' := by
      intro x y
      funext j
      simp only [binaryMaskCoordinate, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split <;> simp
    map_smul' := by
      intro a x
      funext j
      simp only [binaryMaskCoordinate, Pi.smul_apply]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split <;> simp }
  left_inverse := left_inverse

end SymmetricSubgroupAsymptotics

end
