import SymmetricSubgroupAsymptotics.CFSGMatrixCubicUnipotentScalar
import Mathlib.Tactic.NoncommRing

/-! Scalar rigidity for an actual quadratic root unit, including its
nonzero second coefficient. No image restriction is used here. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticRootScalarConjugacy
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem scalar_conjugate_quadratic_root (e d : Matrix I I K)
    (he : e*e=d+d) (hed : e*d=0) (hde : d*e=0) (hdd : d*d=0)
    (j : I) (hej : e j j=0) (hdj : d j j=0)
    (u : (Matrix I I K)ˣ) (t c : K)
    (h : (u:Matrix I I K)*(1+t • e+t^2 • d)*(↑(u⁻¹):Matrix I I K)=c • (1+t • e+t^2 • d)) :
    c=1 := by
  let Y := t • e+t^2 • d
  have hsquare : Y*Y=t^2 • (d+d) := by
    simp only [Y,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,
      he,hed,hde,hdd,smul_zero,add_zero,zero_add,pow_two]
  have hcube : Y^3=0 := by
    rw [show Y^3=Y*Y*Y by noncomm_ring,hsquare]
    simp only [Y,smul_mul_assoc,mul_add,add_mul,mul_smul_comm,
      hde,hdd,smul_zero,add_zero,zero_add]
  have hj : Y j j=0 := by simp only [Y,Matrix.add_apply,Matrix.smul_apply,hej,hdj,smul_zero,add_zero]
  have hj2 : (Y*Y) j j=0 := by
    rw [hsquare]
    simp only [Matrix.smul_apply,Matrix.add_apply,hdj,add_zero,smul_zero]
  apply CFSGMatrixCubicUnipotentScalar.scalar_conjugate_unipotent Y hcube j hj hj2 u c
  simpa only [Y,add_assoc] using h

end SymmetricSubgroupAsymptotics.CFSGQuadraticRootScalarConjugacy
