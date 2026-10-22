import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2RulingPlanes
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-! Actual determinant-zero residual matrices have nonzero outer-product
coordinates. The mixed determinant is the product of the two factor
determinants, the algebraic origin of the two rulings. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

theorem determinant_zero_minors (A : Matrix (Fin 2) (Fin 2) K) (hA : Matrix.det A = 0)
    (i j k l : Fin 2) : A i j * A k l = A i l * A k j := by
  have hh : A 0 0 * A 1 1 = A 0 1 * A 1 0 := by
    exact sub_eq_zero.mp ((Matrix.det_fin_two A).symm.trans hA)
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all [mul_comm]

theorem exists_nonzero_outer_factors (A : Matrix (Fin 2) (Fin 2) K)
    (hne : A ≠ 0) (hdet : Matrix.det A = 0) :
    ∃ u p : Fin 2 → K, u ≠ 0 ∧ p ≠ 0 ∧ A = columnMap K u p := by
  have hij : ∃ i j, A i j ≠ 0 := by
    by_contra hn
    simp only [not_exists, not_not] at hn
    apply hne
    ext i j
    exact hn i j
  obtain ⟨i, j, hij⟩ := hij
  let u := fun k => A k j
  let p := fun k => A i k / A i j
  have hu : u ≠ 0 := by
    intro he
    exact hij (congrFun he i)
  have hp : p ≠ 0 := by
    intro he
    have hh := congrFun he j
    change A i j / A i j = 0 at hh
    rw [div_self hij] at hh
    exact one_ne_zero hh
  refine ⟨u, p, hu, hp, ?_⟩
  ext l k
  change A l k = A l j * (A i k / A i j)
  calc
    A l k = (A i j * A l k) / A i j := by field_simp [hij] <;> ring
    _ = (A i k * A l j) / A i j :=
      congrArg (fun x => x / A i j) (determinant_zero_minors K A hdet i j l k)
    _ = A l j * (A i k / A i j) := by ring

def vectorDet (u v : Fin 2 → K) : K := u 0 * v 1 - u 1 * v 0

theorem outer_sum_determinant (u p v q : Fin 2 → K) :
    Matrix.det (columnMap K u p + columnMap K v q) = vectorDet K u v * vectorDet K p q := by
  rw [Matrix.det_fin_two]
  change (u 0 * p 0 + v 0 * q 0) * (u 1 * p 1 + v 1 * q 1) -
      (u 0 * p 1 + v 0 * q 1) * (u 1 * p 0 + v 1 * q 0) =
    (u 0 * v 1 - u 1 * v 0) * (p 0 * q 1 - p 1 * q 0)
  ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
