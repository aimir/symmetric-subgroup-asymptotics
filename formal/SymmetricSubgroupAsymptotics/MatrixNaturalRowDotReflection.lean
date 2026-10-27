import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixData
import Mathlib.Algebra.BigOperators.Fin

/-! Natural-arithmetic reflection for one actual MatrixData row-dot-column.
Raw coefficient bindings are proved separately, once, before arithmetic.
The checker can use packed natural digits without reducing string parsing
or ZMod multiplication inside the dot loop. No range, field primality,
matrix inverse, whole-operator identity or numerical capacity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.MatrixNaturalRowDotReflection

def rawDigit (rows : Array String) (i j : ℕ) : ℕ :=
  (rows[i]!.toUTF8[j]!).toNat - 48

def natDot (row column : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => natDot row column n + row n * column n

theorem natDot_eq_sum (row column : ℕ → ℕ) (n : ℕ) :
    natDot row column n = ∑ j : Fin n, row j.val * column j.val := by
  induction n with
  | zero => simp only [natDot,Fin.sum_univ_zero]
  | succ n ih =>
    rw [natDot,Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc,Fin.val_last] using
      congrArg (fun t => t + row n * column n) ih

theorem cast_natDot (p n : ℕ) (row column : ℕ → ℕ) :
    (natDot row column n : ZMod p) =
      ∑ j : Fin n, (row j.val : ZMod p) * (column j.val : ZMod p) := by
  rw [natDot_eq_sum]
  simp only [Nat.cast_sum,Nat.cast_mul]

theorem selected_row_dot (p n : ℕ) (rows : Array String) (i z : Fin n)
    (row column : ℕ → ℕ)
    (hrow : ∀ j : Fin n, rawDigit rows i.val j.val = row j.val)
    (hcolumn : ∀ j : Fin n, rawDigit rows j.val z.val = column j.val) :
    (CFSG.Models.MatrixData.matrix p n rows *ᵥ
      (fun j => CFSG.Models.MatrixData.matrix p n rows j z)) i =
        (natDot row column n : ZMod p) := by
  change (∑ j : Fin n,
    (rawDigit rows i.val j.val : ZMod p) * (rawDigit rows j.val z.val : ZMod p)) = _
  calc
    _ = ∑ j : Fin n, (row j.val : ZMod p) * (column j.val : ZMod p) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hrow j,hcolumn j]
    _ = (natDot row column n : ZMod p) := (cast_natDot p n row column).symm

theorem selected_row_dot_mod (p n : ℕ) (rows : Array String) (i z : Fin n)
    (row column : ℕ → ℕ) (target : ℕ)
    (hrow : ∀ j : Fin n, rawDigit rows i.val j.val = row j.val)
    (hcolumn : ∀ j : Fin n, rawDigit rows j.val z.val = column j.val)
    (hcheck : natDot row column n % p = target % p) :
    (CFSG.Models.MatrixData.matrix p n rows *ᵥ
      (fun j => CFSG.Models.MatrixData.matrix p n rows j z)) i = (target : ZMod p) :=
  (selected_row_dot p n rows i z row column hrow hcolumn).trans
    ((ZMod.natCast_eq_natCast_iff' _ _ p).mpr hcheck)

def packedDigit (bits code position : ℕ) : ℕ :=
  code / 2 ^ (bits * position) % 2 ^ bits

def packedDot (bits rowCode columnCode n : ℕ) : ℕ :=
  natDot (packedDigit bits rowCode) (packedDigit bits columnCode) n

theorem selected_packed_row_dot_mod (p n bits : ℕ) (rows : Array String)
    (i z : Fin n) (rowCode columnCode target : ℕ)
    (hrow : ∀ j : Fin n, rawDigit rows i.val j.val = packedDigit bits rowCode j.val)
    (hcolumn : ∀ j : Fin n, rawDigit rows j.val z.val = packedDigit bits columnCode j.val)
    (hcheck : packedDot bits rowCode columnCode n % p = target % p) :
    (CFSG.Models.MatrixData.matrix p n rows *ᵥ
      (fun j => CFSG.Models.MatrixData.matrix p n rows j z)) i = (target : ZMod p) :=
  selected_row_dot_mod p n rows i z (packedDigit bits rowCode)
    (packedDigit bits columnCode) target hrow hcolumn hcheck

end SymmetricSubgroupAsymptotics.MatrixNaturalRowDotReflection
