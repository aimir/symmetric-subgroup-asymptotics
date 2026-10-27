import SymmetricSubgroupAsymptotics.MatrixKroneckerRowStepReflection
import SymmetricSubgroupAsymptotics.SmallNaturalMatrixProductReflection

/-! Whole products of arbitrary cached matrices by packed natural
arithmetic. Neither operand must be a literal MatrixData source matrix.
Raw digit bounds and row/column pack bindings are separate proof data;
each scalar check uses one natural multiplication and middle extraction.
The no-carry bound is the already proved bound for ALL coefficients.
No positive word is expanded by the semantic product theorem. -/
set_option autoImplicit false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
open MatrixKroneckerDotReflection MatrixKroneckerRowStepReflection
open SmallNaturalMatrixProductReflection

theorem entry_eq_of_check {n p q base : ℕ} (hn : 0<n)
    (A B : Matrix (Fin n) (Fin n) (ZMod p)) (i j : Fin n)
    (r c : Fin n → ℕ)
    (hrow : ∀ k,A i k=(r k : ZMod p)) (hcolumn : ∀ k,B k j=(c k : ZMod p))
    (hr : ∀ k,r k<q) (hc : ∀ k,c k<q) (rowCode columnCode target : ℕ)
    (hR : pack base r=rowCode) (hC : reversePack base c=columnCode)
    (hbase : n*(q-1)^2<base)
    (hcheck : (((rowCode*columnCode)/base^(n-1))%base)%p=target%p) :
    (A*B) i j=(target : ZMod p) := by
  rw [Matrix.mul_apply]
  calc
    _=∑ k : Fin n,(r k : ZMod p)*(c k : ZMod p) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hrow k,hcolumn k]
    _=_ := cast_dot_eq_of_check_of_digit_bound hn r c hr hc
      rowCode columnCode target hR hC hbase hcheck

theorem product_eq_of_checks {n p q base : ℕ} (hn : 0<n)
    (A B : Matrix (Fin n) (Fin n) (ZMod p))
    (left right target : Matrix (Fin n) (Fin n) ℕ)
    (hA : A=castMatrix p n left) (hB : B=castMatrix p n right)
    (hleft : ∀ i j,left i j<q) (hright : ∀ i j,right i j<q)
    (rowCode columnCode : Fin n → ℕ)
    (hrow : ∀ i,pack base (left i)=rowCode i)
    (hcolumn : ∀ j,reversePack base (fun i => right i j)=columnCode j)
    (hbase : n*(q-1)^2<base)
    (hcheck : ∀ i j,(((rowCode i*columnCode j)/base^(n-1))%base)%p=target i j%p) :
    A*B=castMatrix p n target := by
  ext i j
  exact entry_eq_of_check hn A B i j (left i) (fun k => right k j)
    (fun k => congrArg (fun M => M i k) hA)
    (fun k => congrArg (fun M => M k j) hB)
    (hleft i) (fun k => hright k j)
    (rowCode i) (columnCode j) (target i j) (hrow i) (hcolumn j) hbase (hcheck i j)

/-- Finite literal cache data. The same row/column bindings can be reused
by every DAG edge that consumes this actual matrix node. -/
structure PackedData (n q base : ℕ) where
  raw : Matrix (Fin n) (Fin n) ℕ
  digit_lt : ∀ i j,raw i j<q
  rowCode : Fin n → ℕ
  columnCode : Fin n → ℕ
  row_binding : ∀ i,pack base (raw i)=rowCode i
  column_binding : ∀ j,reversePack base (fun i => raw i j)=columnCode j

def PackedData.matrix {n q base : ℕ} (D : PackedData n q base) (p : ℕ) :
    Matrix (Fin n) (Fin n) (ZMod p) := castMatrix p n D.raw

theorem product_eq_of_data {n p q base : ℕ} (hn : 0<n)
    (A B : Matrix (Fin n) (Fin n) (ZMod p)) (U V W : PackedData n q base)
    (hA : A=U.matrix p) (hB : B=V.matrix p)
    (hbase : n*(q-1)^2<base)
    (hcheck : ∀ i j,(((U.rowCode i*V.columnCode j)/base^(n-1))%base)%p=W.raw i j%p) :
    A*B=W.matrix p :=
  product_eq_of_checks hn A B U.raw V.raw W.raw hA hB U.digit_lt V.digit_lt
    U.rowCode V.columnCode U.row_binding V.column_binding hbase hcheck

theorem eq_one_of_raw {n p q base : ℕ}
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (D : PackedData n q base)
    (hA : A=D.matrix p) (hraw : D.raw=1) : A=1 := by
  exact hA.trans (by rw [PackedData.matrix,hraw,castMatrix_one])

end SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
