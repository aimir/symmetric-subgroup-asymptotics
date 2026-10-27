import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowVectorReflection

/-! Transfer checked original source-column bindings to the row interface
using ONLY a pure packed-Nat transpose certificate. No native coefficient
string is decoded again, and no field/group/order assumption is needed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.MatrixPackedColumnTransposeRowBinding
open MatrixNaturalRowDotReflection

theorem row_binding_of_column_transpose (n bits : ℕ) (rows : Array String)
    (columnCode rowCode : ℕ → ℕ)
    (hcolumn : ∀ z i : Fin n,
      rawDigit rows i.val z.val=packedDigit bits (columnCode z.val) i.val)
    (htranspose : ∀ i j : Fin n,
      packedDigit bits (columnCode j.val) i.val=packedDigit bits (rowCode i.val) j.val) :
    ∀ i j : Fin n,rawDigit rows i.val j.val=packedDigit bits (rowCode i.val) j.val := by
  intro i j
  exact (hcolumn j i).trans (htranspose i j)

end SymmetricSubgroupAsymptotics.MatrixPackedColumnTransposeRowBinding
