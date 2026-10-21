import SymmetricSubgroupAsymptotics.CFSGSuzukiDiagonalTorus

/-! The original Suzuki Weyl matrix inverts the original diagonal torus,
also in its exact normalized parameter chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiTorus
open CFSGSuzukiFieldParameters

theorem weyl_torus_conjugation (m : ℕ) (c : (Field m)ˣ) :
    weylElement m*torusElement m c*(weylElement m)⁻¹=torusElement m c⁻¹ := by
  rw [weylElement_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul,torusElement_coe,weylElement_coe,
      CFSG.Models.SuzukiConstruction.torus,CFSG.Models.SuzukiConstruction.weyl,
      Matrix.mul_apply,Matrix.vecMul_diagonal,Fin.sum_univ_succ]

theorem weyl_normalizedTorus_conjugation (m : ℕ) (c : (Field m)ˣ) :
    weylElement m*normalizedTorusElement m c*(weylElement m)⁻¹=
      normalizedTorusElement m c⁻¹ := by
  dsimp only [normalizedTorusElement]
  rw [weyl_torus_conjugation]
  apply congrArg (torusElement m)
  apply Units.ext
  change (inverseTorusParameter m (c : Field m))⁻¹=
    inverseTorusParameter m ((c⁻¹ : (Field m)ˣ) : Field m)
  rw [Units.val_inv_eq_inv_val]
  change ((c : Field m)^2/theta m (c : Field m))⁻¹=
    ((c : Field m)⁻¹)^2/theta m ((c : Field m)⁻¹)
  rw [map_inv₀]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,inv_pow]
  ac_rfl

end SymmetricSubgroupAsymptotics.CFSGSuzukiTorus
