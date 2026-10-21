import SymmetricSubgroupAsymptotics.CFSGMatrixUnipotentScalar

/-! Scalar conjugacy cannot disguise a cubic unipotent when one
coordinate has zero diagonal in both nilpotent powers. This covers
quadratic short-root exponentials without a square-zero shortcut. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMatrixCubicUnipotentScalar
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem scalar_shift_cube_zero (Y : Matrix I I K) (hY : Y^3=0) (j : I)
    (hj : Y j j=0) (hj2 : (Y*Y) j j=0) (c : K)
    (h : (c • (1+Y)-1)^3=0) : c=1 := by
  have hshift : c • (1+Y)-1=(c-1) • (1:Matrix I I K)+c • Y := by
    simp only [smul_add,sub_smul,one_smul]
    abel
  have h3 : Y*(Y*Y)=0 := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hY
  rw [hshift] at h
  have hh := congrArg (fun M : Matrix I I K=>M j j) h
  simp only [pow_succ,pow_zero,one_mul,add_mul,mul_add,smul_mul_assoc,
    mul_smul_comm,smul_smul,mul_one,mul_assoc,h3,smul_zero,
    Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,Matrix.zero_apply,
    hj,hj2,smul_eq_mul,mul_zero,mul_one,zero_add,add_zero] at hh
  have hp : (c-1)^3=0 := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hh
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hp)

theorem conjugate_shift_cube_zero (Y : Matrix I I K) (hY : Y^3=0)
    (u : (Matrix I I K)ˣ) :
    ((u:Matrix I I K)*(1+Y)*(↑(u⁻¹):Matrix I I K)-1)^3=0 := by
  have hshift : (u:Matrix I I K)*(1+Y)*(↑(u⁻¹):Matrix I I K)-1=
      (u:Matrix I I K)*Y*(↑(u⁻¹):Matrix I I K) := by
    rw [mul_add,add_mul,mul_one,Units.mul_inv,add_sub_cancel_left]
  rw [hshift]
  calc
    ((u:Matrix I I K)*Y*(↑(u⁻¹):Matrix I I K))^3=
        (u:Matrix I I K)*(Y^3)*(↑(u⁻¹):Matrix I I K) := by
      simp only [pow_succ,pow_zero,one_mul,mul_assoc,Units.inv_mul_cancel_left]
    _=0 := by rw [hY,mul_zero,zero_mul]

theorem scalar_conjugate_unipotent (Y : Matrix I I K) (hY : Y^3=0)
    (j : I) (hj : Y j j=0) (hj2 : (Y*Y) j j=0) (u : (Matrix I I K)ˣ) (c : K)
    (h : (u:Matrix I I K)*(1+Y)*(↑(u⁻¹):Matrix I I K)=c • (1+Y)) : c=1 := by
  apply scalar_shift_cube_zero Y hY j hj hj2 c
  rw [←h]
  exact conjugate_shift_cube_zero Y hY u

end SymmetricSubgroupAsymptotics.CFSGMatrixCubicUnipotentScalar
