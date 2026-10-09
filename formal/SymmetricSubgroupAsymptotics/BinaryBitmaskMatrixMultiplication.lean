import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates

/-!
# Fast multiplication certificates for binary column masks

Large finite representations store a binary matrix by one natural-number
mask per column.  Multiplying the decoded matrices entry by entry is much
more expensive than composing those masks.  This file proves once and for
all that xor-summing the selected left columns computes a product column.
Generated certificates can therefore check representation transitions with
native natural-number operations and transport the result to literal matrix
multiplication.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Natural-number masks with xor as addition. -/
@[ext]
structure BinaryXorMask where
  val : ℕ

namespace BinaryXorMask

instance : Zero BinaryXorMask := ⟨⟨0⟩⟩
instance : Add BinaryXorMask := ⟨fun x y ↦ ⟨x.val ^^^ y.val⟩⟩

@[simp] theorem val_zero : (0 : BinaryXorMask).val = 0 := rfl
@[simp] theorem val_add (x y : BinaryXorMask) : (x + y).val = x.val ^^^ y.val := rfl

instance : AddCommMonoid BinaryXorMask where
  add_assoc x y z := by ext; exact Nat.xor_assoc x.val y.val z.val
  zero_add x := by
    ext
    change 0 ^^^ x.val = x.val
    exact Nat.zero_xor x.val
  add_zero x := by
    ext
    change x.val ^^^ 0 = x.val
    exact Nat.xor_zero x.val
  add_comm x y := by ext; exact Nat.xor_comm x.val y.val
  nsmul := nsmulRec

/-- Reading one bit is an additive map from xor masks to `ZMod 2`. -/
def bitHom (i : ℕ) : BinaryXorMask →+ ZMod 2 where
  toFun x := if x.val.testBit i then 1 else 0
  map_zero' := by simp
  map_add' x y := by
    change (if (x.val ^^^ y.val).testBit i then 1 else 0) =
      (if x.val.testBit i then 1 else 0) +
        (if y.val.testBit i then 1 else 0)
    rw [Nat.testBit_xor]
    cases hx : x.val.testBit i <;> cases hy : y.val.testBit i <;>
      simp [hx, hy] <;> native_decide

end BinaryXorMask

/-- The mask of a linear combination of the displayed binary columns. -/
def binaryMaskLinearCombination (d : ℕ) (columns : Fin d → ℕ)
    (coefficients : ℕ) : ℕ :=
  (∑ j : Fin d,
    if coefficients.testBit j.val then
      (⟨columns j⟩ : BinaryXorMask)
    else 0).val

/-- Decoding the xor combination agrees with literal matrix-vector
multiplication over `ZMod 2`. -/
theorem binaryVectorOfMask_linearCombination (d : ℕ)
    (columns : Fin d → ℕ) (coefficients : ℕ) :
    binaryVectorOfMask d
        (binaryMaskLinearCombination d columns coefficients) =
      (binaryMatrixOfColumnMasks d columns).mulVec
        (binaryVectorOfMask d coefficients) := by
  funext i
  change (BinaryXorMask.bitHom i.val)
      (∑ j : Fin d,
        if coefficients.testBit j.val then
          (⟨columns j⟩ : BinaryXorMask)
        else 0) = _
  rw [map_sum]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : coefficients.testBit j.val
  · simp [h, BinaryXorMask.bitHom, binaryMatrixOfColumnMasks,
      binaryVectorOfMask]
  · simp [h, BinaryXorMask.bitHom, binaryMatrixOfColumnMasks,
      binaryVectorOfMask]

/-- A pointwise certificate for the product column masks proves equality of
the decoded binary matrices. -/
theorem binaryMatrixOfColumnMasks_mul_of_columns
    (d : ℕ) (left right product : Fin d → ℕ)
    (h : ∀ j,
      product j = binaryMaskLinearCombination d left (right j)) :
    binaryMatrixOfColumnMasks d product =
      binaryMatrixOfColumnMasks d left *
        binaryMatrixOfColumnMasks d right := by
  ext i j
  have hv := congrFun
    (binaryVectorOfMask_linearCombination d left (right j)) i
  change (if (product j).testBit i.val then 1 else 0) = _
  rw [h j]
  simpa only [binaryVectorOfMask, binaryMatrixOfColumnMasks,
    Matrix.mul_apply, Matrix.mulVec, dotProduct] using hv

end SymmetricSubgroupAsymptotics

end
