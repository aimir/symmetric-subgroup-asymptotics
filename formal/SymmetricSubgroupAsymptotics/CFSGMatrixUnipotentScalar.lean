import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Abel

/-! Scalar multiples cannot disguise a square-zero matrix transvection
under conjugacy over a field. This supplies the projective-centre step
without determinant or order formulas, including defining characteristic. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMatrixUnipotentScalar
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem scalar_shift_sq_zero (E : Matrix I I K) (he : E * E = 0)
    (j : I) (hdiag : E j j = 0) (t c : K)
    (h : (c • (1 + t • E) - 1) ^ 2 = 0) : c = 1 := by
  have hshift : c • (1 + t • E) - 1 =
      (c - 1) • (1 : Matrix I I K) + (c * t) • E := by
    simp only [smul_add, smul_smul, sub_smul, one_smul]
    abel
  rw [hshift] at h
  have hh := congrArg (fun M : Matrix I I K => M j j) h
  simp only [pow_two, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, one_mul, mul_one, he, smul_zero, add_zero,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.zero_apply, hdiag, smul_eq_mul, mul_zero, mul_one, add_zero] at hh
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hh)

theorem conjugate_transvection_sq_zero (E : Matrix I I K) (he : E * E = 0)
    (u : (Matrix I I K)ˣ) (t : K) :
    ((u : Matrix I I K) * (1 + t • E) * (↑(u⁻¹) : Matrix I I K) - 1) ^ 2 = 0 := by
  have hx : (t • E) * (t • E) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, he, smul_zero]
  have hshift : (u : Matrix I I K) * (1 + t • E) * (↑(u⁻¹) : Matrix I I K) - 1 =
      (u : Matrix I I K) * (t • E) * (↑(u⁻¹) : Matrix I I K) := by
    rw [mul_add, add_mul, mul_one, Units.mul_inv, add_sub_cancel_left]
  rw [hshift]
  calc
    ((u : Matrix I I K) * (t • E) * (↑(u⁻¹) : Matrix I I K)) ^ 2 =
        (u : Matrix I I K) * ((t • E) * (t • E)) * (↑(u⁻¹) : Matrix I I K) := by
      simp only [pow_two, mul_assoc, Units.inv_mul_cancel_left]
    _ = 0 := by rw [hx, mul_zero, zero_mul]

theorem scalar_conjugate_transvection (E : Matrix I I K) (he : E * E = 0)
    (j : I) (hdiag : E j j = 0) (u : (Matrix I I K)ˣ) (t c : K)
    (h : (u : Matrix I I K) * (1 + t • E) * (↑(u⁻¹) : Matrix I I K) = c • (1 + t • E)) :
    c = 1 := by
  apply scalar_shift_sq_zero E he j hdiag t c
  rw [← h]
  exact conjugate_transvection_sq_zero E he u t

end SymmetricSubgroupAsymptotics.CFSGMatrixUnipotentScalar
