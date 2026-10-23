import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Abel

/-! Literal square-zero two-plane shears on two disjoint coordinate
pairs. This is sparse matrix algebra only; the subsequent unitary
installer supplies the actual signed-form equation and original fixed
group membership. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearArrays
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def array (p q : Fin 2 → I) (B : Matrix (Fin 2) (Fin 2) K) : Matrix I I K :=
  ∑ i, ∑ j, Matrix.single (p i) (q j) (B i j)

omit [Fintype I] in
theorem array_zero (p q : Fin 2 → I) : array p q (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  simp only [array, Matrix.zero_apply, Matrix.single_zero, Finset.sum_const_zero]

omit [Fintype I] in
theorem array_add (p q : Fin 2 → I) (A B : Matrix (Fin 2) (Fin 2) K) :
    array p q (A + B) = array p q A + array p q B := by
  simp only [array, Matrix.add_apply, Matrix.single_add, Finset.sum_add_distrib]

omit [Fintype I] in
theorem array_entry (p q : Fin 2 → I) (hp : Function.Injective p)
    (hq : Function.Injective q) (B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    array p q B (p i) (q j) = B i j := by
  simp [array, Matrix.sum_apply, Matrix.single_apply, hp.eq_iff, hq.eq_iff, ite_and]

omit [Fintype I] in
theorem array_injective (p q : Fin 2 → I) (hp : Function.Injective p)
    (hq : Function.Injective q) : Function.Injective (array p q (K := K)) := by
  intro A B h
  ext i j
  have he := congrArg (fun M : Matrix I I K => M (p i) (q j)) h
  simpa only [array_entry p q hp hq] using he

theorem array_mul_array (p q : Fin 2 → I) (hdisj : ∀ i j, q i ≠ p j)
    (A B : Matrix (Fin 2) (Fin 2) K) : array p q A * array p q B = 0 := by
  simp only [array, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  apply Matrix.single_mul_single_of_ne
  exact hdisj l i

def unit (p q : Fin 2 → I) (hdisj : ∀ i j, q i ≠ p j)
    (B : Matrix (Fin 2) (Fin 2) K) : (Matrix I I K)ˣ where
  val := 1 + array p q B
  inv := 1 - array p q B
  val_inv := by
    simp only [mul_sub, add_mul, one_mul, mul_one, array_mul_array p q hdisj]
    abel
  inv_val := by
    simp only [mul_add, sub_mul, one_mul, mul_one, array_mul_array p q hdisj]
    abel

theorem unit_zero (p q : Fin 2 → I) (hdisj : ∀ i j, q i ≠ p j) :
    unit p q hdisj (0 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  apply Units.ext
  change 1 + array p q 0 = 1
  rw [array_zero, add_zero]

theorem unit_add (p q : Fin 2 → I) (hdisj : ∀ i j, q i ≠ p j)
    (A B : Matrix (Fin 2) (Fin 2) K) :
    unit p q hdisj (A + B) = unit p q hdisj A * unit p q hdisj B := by
  apply Units.ext
  change 1 + array p q (A + B) = (1 + array p q A) * (1 + array p q B)
  rw [array_add]
  simp only [mul_add, add_mul, one_mul, mul_one, array_mul_array p q hdisj]
  abel

theorem unit_injective (p q : Fin 2 → I) (hp : Function.Injective p)
    (hq : Function.Injective q) (hdisj : ∀ i j, q i ≠ p j) :
    Function.Injective (unit p q hdisj (K := K)) := by
  intro A B h
  apply array_injective p q hp hq
  have he := congrArg (fun g : (Matrix I I K)ˣ => (g : Matrix I I K)) h
  exact add_left_cancel he

end SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearArrays
