import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointTriple

/-! Rational conjugation on a genuine length-four adjoint string. The
fourth coefficient is proved zero from the displayed fourth-adjoint
condition. No uniform nilpotence of the original Serre algebra is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem canonicalRoot_conjugation_of_fourth_lie (neg : Bool) (i : Fin r)
    (X : Matrix I I ℚ)
    (hx : ⁅fieldRoot D ℚ neg i,
      ⁅fieldRoot D ℚ neg i, ⁅fieldRoot D ℚ neg i, ⁅fieldRoot D ℚ neg i, X⁆⁆⁆⁆ = 0)
    (t : ℚ) :
    (canonicalRoot D ℚ neg i t : Matrix I I ℚ) * X *
      (((canonicalRoot D ℚ neg i t)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ) =
      X + t • ⁅fieldRoot D ℚ neg i, X⁆ +
        (t ^ 2 / 2) • ⁅fieldRoot D ℚ neg i, ⁅fieldRoot D ℚ neg i, X⁆⁆ +
        (t ^ 3 / 6) •
          ⁅fieldRoot D ℚ neg i, ⁅fieldRoot D ℚ neg i, ⁅fieldRoot D ℚ neg i, X⁆⁆⁆ := by
  let E := fieldRoot D ℚ neg i
  let d := fieldSecond D ℚ neg i
  have hop (k : ℕ) : CFSGIntegralQuadraticRootOperators.operator ℚ E d k X =
      (k.factorial : ℚ)⁻¹ • ((LieAlgebra.ad ℚ (Matrix I I ℚ) E) ^ k) X := by
    calc
      _ = CFSGSquareZeroDividedPowers.operator E k X :=
        (CFSGQuadraticRootDividedPowers.rational_operator E d
          (fieldRoot_square D ℚ neg i) (fieldRoot_mul_second D ℚ neg i)
          (fieldSecond_mul_root D ℚ neg i) k X).symm
      _ = _ := rfl
  have had4 : ((LieAlgebra.ad ℚ (Matrix I I ℚ) E) ^ 4) X = 0 := hx
  have h1 : CFSGIntegralQuadraticRootOperators.operator ℚ E d 1 X = ⁅E, X⁆ := by
    rw [CFSGIntegralQuadraticRootOperators.operator_one]
    rfl
  have h2 : CFSGIntegralQuadraticRootOperators.operator ℚ E d 2 X =
      (1 / 2 : ℚ) • ⁅E, ⁅E, X⁆⁆ := by
    rw [hop]
    change (2 : ℚ)⁻¹ • ⁅E, ⁅E, X⁆⁆ = (1 / 2 : ℚ) • ⁅E, ⁅E, X⁆⁆
    rw [one_div]
  have h3 : CFSGIntegralQuadraticRootOperators.operator ℚ E d 3 X =
      (1 / 6 : ℚ) • ⁅E, ⁅E, ⁅E, X⁆⁆⁆ := by
    rw [hop]
    change (6 : ℚ)⁻¹ • ⁅E, ⁅E, ⁅E, X⁆⁆⁆ = (1 / 6 : ℚ) • ⁅E, ⁅E, ⁅E, X⁆⁆⁆
    rw [one_div]
  have h4 : CFSGIntegralQuadraticRootOperators.operator ℚ E d 4 X = 0 := by
    rw [hop, had4, smul_zero]
  have hh := CFSGIntegralQuadraticRootOperators.operator_sum_eq_conjugation ℚ t E d X
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    CFSGIntegralQuadraticRootOperators.operator_zero, h1, h2, h3, h4,
    pow_zero, pow_one, one_smul, smul_zero, add_zero, smul_smul] at hh
  rw [show t ^ 2 * (1 / 2 : ℚ) = t ^ 2 / 2 by ring,
    show t ^ 3 * (1 / 6 : ℚ) = t ^ 3 / 6 by ring] at hh
  have hu : (canonicalRoot D ℚ neg i t : Matrix I I ℚ) =
      CFSGIntegralQuadraticRootOperators.exponential ℚ E d t := by
    rw [canonicalRoot_val]
    rfl
  have hui : (((canonicalRoot D ℚ neg i t)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ) =
      CFSGIntegralQuadraticRootOperators.exponential ℚ E d (-t) := by
    rw [canonicalRoot_inverse, canonicalRoot_val]
    rfl
  rw [hu, hui]
  exact hh.symm

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
