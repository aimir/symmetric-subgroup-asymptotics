import SymmetricSubgroupAsymptotics.MatrixNaturalRowDotReflection

/-! Staged reflection of ONE selected row of an actual matrix power.
The certificate retains every column of that row, but never asserts a
whole-matrix identity. Raw source-column bindings and modular dot checks
are explicit obligations, separate from any group-generator conclusion. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.MatrixNaturalRowPowerReflection
open MatrixNaturalRowDotReflection

theorem packed_row_step (p n bits : ℕ) (rows : Array String)
    (rowCode nextCode : ℕ) (columnCode : ℕ → ℕ)
    (hcolumn : ∀ (z j : Fin n),
      rawDigit rows j.val z.val = packedDigit bits (columnCode z.val) j.val)
    (hcheck : ∀ z : Fin n,
      packedDot bits rowCode (columnCode z.val) n % p =
        packedDigit bits nextCode z.val % p) (z : Fin n) :
    (∑ j : Fin n, (packedDigit bits rowCode j.val : ZMod p) *
      CFSG.Models.MatrixData.matrix p n rows j z) =
        (packedDigit bits nextCode z.val : ZMod p) := by
  calc
    _ = ∑ j : Fin n, (packedDigit bits rowCode j.val : ZMod p) *
        (packedDigit bits (columnCode z.val) j.val : ZMod p) := by
      apply Finset.sum_congr rfl
      intro j _
      change (packedDigit bits rowCode j.val : ZMod p) * (rawDigit rows j.val z.val : ZMod p) = _
      rw [hcolumn z j]
    _ = (packedDot bits rowCode (columnCode z.val) n : ZMod p) :=
      (cast_natDot p n (packedDigit bits rowCode)
        (packedDigit bits (columnCode z.val))).symm
    _ = _ := (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (hcheck z)

theorem matrix_pow_row_eq (p n : ℕ) (rows : Array String) (i : Fin n)
    (e : ℕ) (v : ℕ → Fin n → ZMod p)
    (hzero : ∀ z : Fin n, v 0 z = (1 : Matrix (Fin n) (Fin n) (ZMod p)) i z)
    (hstep : ∀ k : ℕ, k < e → ∀ z : Fin n,
      v (k+1) z = ∑ j : Fin n, v k j * CFSG.Models.MatrixData.matrix p n rows j z) :
    ∀ z : Fin n, (CFSG.Models.MatrixData.matrix p n rows ^ e) i z = v e z := by
  have aux : ∀ k : ℕ, k ≤ e → ∀ z : Fin n,
      (CFSG.Models.MatrixData.matrix p n rows ^ k) i z = v k z := by
    intro k
    induction k with
    | zero =>
      intro _ z
      simpa only [pow_zero] using (hzero z).symm
    | succ k ih =>
      intro hk z
      rw [pow_succ,Matrix.mul_apply]
      calc
        _ = ∑ j : Fin n, v k j * CFSG.Models.MatrixData.matrix p n rows j z := by
          apply Finset.sum_congr rfl
          intro j _
          rw [ih (Nat.le_of_succ_le hk) j]
        _ = v (k+1) z := (hstep k (Nat.lt_of_succ_le hk) z).symm
  exact aux e le_rfl

end SymmetricSubgroupAsymptotics.MatrixNaturalRowPowerReflection
