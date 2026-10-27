import SymmetricSubgroupAsymptotics.MatrixModelSelectedProductPrimePeriod

/-! A literal coefficient binding for ONE chosen row and a packed scalar
check give the actual coordinate of the original matrix-vector product.
This is independent of all other rows and does not assert a vector period,
whole matrix equation, array invertibility or named model identification. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.MatrixModelSelectedRowVectorReflection
open MatrixNaturalRowDotReflection MatrixModelSelectedPointPeriodTwo

theorem coordinate_step (p n bits : ℕ) (rows : Array String) (i : Fin n)
    (rowCode inputCode nextCode : ℕ)
    (hrow : ∀ j : Fin n,rawDigit rows i.val j.val=packedDigit bits rowCode j.val)
    (hcheck : packedDot bits rowCode inputCode n % p=
      packedDigit bits nextCode i.val % p) :
    (CFSG.Models.MatrixData.matrix p n rows *ᵥ
      (fun j : Fin n => (packedDigit bits inputCode j.val : ZMod p))) i=
      (packedDigit bits nextCode i.val : ZMod p) := by
  change (∑ j : Fin n,(rawDigit rows i.val j.val : ZMod p)*
    (packedDigit bits inputCode j.val : ZMod p))=_
  calc
    _=∑ j : Fin n,(packedDigit bits rowCode j.val : ZMod p)*
        (packedDigit bits inputCode j.val : ZMod p) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hrow j]
    _=(packedDot bits rowCode inputCode n : ZMod p) :=
      (cast_natDot p n (packedDigit bits rowCode) (packedDigit bits inputCode)).symm
    _=_ := (ZMod.natCast_eq_natCast_iff' _ _ p).mpr hcheck

end SymmetricSubgroupAsymptotics.MatrixModelSelectedRowVectorReflection
