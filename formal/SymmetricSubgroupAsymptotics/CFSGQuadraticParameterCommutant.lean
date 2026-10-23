import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! Two distinct nonzero parameters separate the true linear and
quadratic coefficients of a root word in every characteristic. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticParameterCommutant
variable {K B : Type*} [Field K] [Ring B] [Algebra K B]

theorem commute_of_two_parameters (A E D : B) (c : K) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (h1 : A * (1 + E + D) = (1 + E + D) * A)
    (hc : A * (1 + c • E + c ^ 2 • D) = (1 + c • E + c ^ 2 • D) * A) :
    A * E = E * A ∧ A * D = D * A := by
  let S : Submodule K B :=
    { carrier := {x | A * x = x * A}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change A * x = x * A at hx
        change A * y = y * A at hy
        change A * (x + y) = (x + y) * A
        rw [mul_add, add_mul, hx, hy]
      smul_mem' := by
        intro a x hx
        change A * x = x * A at hx
        change A * (a • x) = (a • x) * A
        rw [mul_smul_comm, smul_mul_assoc, hx] }
  have hone : E + D ∈ S := by
    change A * (E + D) = (E + D) * A
    apply add_left_cancel (a := A)
    simpa only [mul_add, add_mul, mul_one, one_mul, add_assoc] using h1
  have hlinear : c • E + c ^ 2 • D ∈ S := by
    change A * (c • E + c ^ 2 • D) = (c • E + c ^ 2 • D) * A
    apply add_left_cancel (a := A)
    simpa only [mul_add, add_mul, mul_one, one_mul, add_assoc] using hc
  have hquad : (c ^ 2 - c) • D ∈ S := by
    have h := S.sub_mem hlinear (S.smul_mem c hone)
    convert h using 1 <;> module
  have hd : c ^ 2 - c ≠ 0 := by
    have he : c ^ 2 - c = c * (c - 1) := by ring
    rw [he]
    exact mul_ne_zero hc0 (sub_ne_zero.mpr hc1)
  have hD : D ∈ S := by
    have h := S.smul_mem (c ^ 2 - c)⁻¹ hquad
    simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using h
  have hE : E ∈ S := by
    have h := S.sub_mem hone hD
    simpa only [add_sub_cancel_right] using h
  exact ⟨hE, hD⟩

theorem commute_of_all_parameters (A E D : B) (c : K) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (h : ∀ t : K, A * (1 + t • E + t ^ 2 • D) =
      (1 + t • E + t ^ 2 • D) * A) :
    A * E = E * A ∧ A * D = D * A := by
  apply commute_of_two_parameters A E D c hc0 hc1
  · simpa only [one_smul, one_pow] using h 1
  · exact h c

end SymmetricSubgroupAsymptotics.CFSGQuadraticParameterCommutant
