import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-! A commuting product of square-zero root displacements has square
exactly twice the mixed product. This is a literal ring identity, the
first algebraic step in recognizing polar-line adjacency intrinsically. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSquareZeroRootProducts
variable {R : Type*} [Ring R]

theorem unit_conjugate_squareZero (g : Rˣ) (A : R) (hA : A ^ 2 = 0) :
    ((g : R) * A * (↑(g⁻¹) : R)) ^ 2 = 0 := by
  rw [pow_two]
  calc
    ((g : R) * A * (↑(g⁻¹) : R)) * ((g : R) * A * (↑(g⁻¹) : R)) =
        (g : R) * A * ((↑(g⁻¹) : R) * (g : R)) * A * (↑(g⁻¹) : R) := by
      noncomm_ring
    _ = 0 := by
      rw [Units.inv_mul, mul_one, mul_assoc (g : R) A A, ← pow_two, hA, mul_zero, zero_mul]

theorem commuting_squareZero_sum_square (A B : R) (hA : A * A = 0) (hB : B * B = 0)
    (hc : Commute A B) :
    (A + B + A * B) ^ 2 = 2 • (A * B) := by
  have hAC : A * (A * B) = 0 := by rw [← mul_assoc, hA, zero_mul]
  have hCA : (A * B) * A = 0 := by rw [mul_assoc, ← hc.eq, hAC]
  have hCB : (A * B) * B = 0 := by rw [mul_assoc, hB, mul_zero]
  have hBC : B * (A * B) = 0 := by rw [← mul_assoc, ← hc.eq, hCB]
  have hCC : (A * B) * (A * B) = 0 := by rw [← mul_assoc, hCA, zero_mul]
  simp only [pow_two, add_mul, mul_add, hA, hB, hAC, hCA, hCB, hBC, hCC,
    ← hc.eq, zero_add, add_zero, two_nsmul]

theorem commuting_units_displacement_square (u v : Rˣ)
    (hu : ((u : R) - 1) ^ 2 = 0) (hv : ((v : R) - 1) ^ 2 = 0)
    (hc : Commute u v) :
    (((u * v : Rˣ) : R) - 1) ^ 2 = 2 • (((u : R) - 1) * ((v : R) - 1)) := by
  have hxy : (u : R) * (v : R) = (v : R) * (u : R) := congrArg Units.val hc.eq
  have hAB : Commute ((u : R) - 1) ((v : R) - 1) := by
    change ((u : R) - 1) * ((v : R) - 1) = ((v : R) - 1) * ((u : R) - 1)
    simp only [sub_mul, mul_sub, one_mul, mul_one, hxy]
    abel
  have he : ((u * v : Rˣ) : R) - 1 =
      ((u : R) - 1) + ((v : R) - 1) + ((u : R) - 1) * ((v : R) - 1) := by
    change (u : R) * (v : R) - 1 = _
    noncomm_ring
  rw [he]
  exact commuting_squareZero_sum_square _ _ (by simpa only [pow_two] using hu)
    (by simpa only [pow_two] using hv) hAB

end SymmetricSubgroupAsymptotics.CFSGSquareZeroRootProducts
