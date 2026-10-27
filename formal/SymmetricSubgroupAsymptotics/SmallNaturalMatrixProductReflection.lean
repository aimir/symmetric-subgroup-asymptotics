import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Small natural dot-product reflection. Literal coefficient bindings and
all whole-matrix entries remain in the kernel; there is no word/order oracle. -/
set_option autoImplicit false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.SmallNaturalMatrixProductReflection

def castMatrix (p n : ℕ) (r : Matrix (Fin n) (Fin n) ℕ) :
    Matrix (Fin n) (Fin n) (ZMod p) := fun i j => (r i j : ZMod p)

theorem castMatrix_one (p n : ℕ) : castMatrix p n 1=1 := by
  classical
  ext i j
  simp only [castMatrix,Matrix.one_apply]
  split_ifs <;> simp

theorem castMatrix_mul (p n : ℕ) (r s : Matrix (Fin n) (Fin n) ℕ) :
    castMatrix p n (r*s)=castMatrix p n r*castMatrix p n s := by
  ext i j
  simp only [castMatrix,Matrix.mul_apply,Nat.cast_sum,Nat.cast_mul]

theorem mul_eq_of_mod_dot (p n : ℕ) (r s t : Matrix (Fin n) (Fin n) ℕ)
    (h : ∀ i j,(∑ k : Fin n,r i k*s k j)%p=t i j%p) :
    castMatrix p n r*castMatrix p n s=castMatrix p n t := by
  ext i j
  change (∑ k : Fin n,(r i k : ZMod p)*(s k j : ZMod p))=(t i j : ZMod p)
  have hc : (((∑ k : Fin n,r i k*s k j) : ℕ) : ZMod p)=(t i j : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (h i j)
  simpa only [Nat.cast_sum,Nat.cast_mul] using hc

end SymmetricSubgroupAsymptotics.SmallNaturalMatrixProductReflection
