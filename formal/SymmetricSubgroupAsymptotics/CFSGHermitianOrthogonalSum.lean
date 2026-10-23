import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan

/-! Exact norm decomposition on an orthogonal Hermitian sum, with its
genuine sigma coefficient retained in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem hermitian_orthogonal_sum_self (sigma : K ≃+* K) (H : Matrix I I K)
    (x y : I → K) (a : K) (hxy : hermitianPair sigma H x y = 0)
    (hyx : hermitianPair sigma H y x = 0) :
    hermitianPair sigma H (x + a • y) (x + a • y) =
      hermitianPair sigma H x x + sigma a * a * hermitianPair sigma H y y := by
  have hxs := hermitianPair_smul sigma H 1 a x y
  have hsx := hermitianPair_smul sigma H a 1 y x
  have hss := hermitianPair_smul sigma H a a y y
  simp only [one_smul, map_one, one_mul, mul_one, hxy, hyx, mul_zero] at hxs hsx
  rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right, hxs, hsx, hss]
  simp only [add_zero, zero_add]

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
