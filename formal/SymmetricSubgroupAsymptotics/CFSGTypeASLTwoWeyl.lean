import SymmetricSubgroupAsymptotics.CFSGTypeARootTorus
import Mathlib.Tactic.FinCases

/-! The actual two-coordinate Weyl word and its symbolic actions. No
finite group is enumerated, and the scalar field stays arbitrary. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeASLTwoWeyl
open Matrix CFSGTypeAElementaryMatrices CFSGTypeARootTorus
variable {F : Type*} [Field F]

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) F

def upper (a : F) : SL2 (F:=F) := elementary (by decide : (0 : Fin 2)≠1) a

def lower (a : F) : SL2 (F:=F) := elementary (by decide : (1 : Fin 2)≠0) a

def weyl : SL2 (F:=F) := upper 1*lower (-1)*upper 1

theorem weyl_upper (a : F) :
    weyl*upper a*weyl⁻¹=lower (-a) := by
  have hm : weyl*upper a=lower (-a)*weyl := by
    apply Subtype.ext
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [weyl,upper,lower,elementary,Matrix.mul_apply,Fin.sum_univ_two,
        Matrix.transvection,Matrix.single_apply,Matrix.one_apply] <;> ring
  have hc := congrArg (fun X : SL2 (F:=F) => X*weyl⁻¹) hm
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using hc

theorem weyl_torus (g : Fˣ) :
    weyl*torus (by decide : (0 : Fin 2)≠1) g*weyl⁻¹=
      torus (by decide : (0 : Fin 2)≠1) g⁻¹ := by
  have hm : weyl*torus (by decide : (0 : Fin 2)≠1) g=
      torus (by decide : (0 : Fin 2)≠1) g⁻¹*weyl := by
    apply Subtype.ext
    change weyl.val*(torus (by decide : (0 : Fin 2)≠1) g).val=
      (torus (by decide : (0 : Fin 2)≠1) g⁻¹).val*weyl.val
    rw [torus_coe,torus_coe]
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [weyl,upper,lower,elementary,Matrix.diagonal_mul,Matrix.mul_diagonal,
        Matrix.mul_apply,Fin.sum_univ_two,Matrix.transvection,Matrix.single_apply,
        Matrix.one_apply,Units.val_inv_eq_inv_val] <;> ring
  have hc := congrArg (fun X : SL2 (F:=F) => X*weyl⁻¹) hm
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using hc

end SymmetricSubgroupAsymptotics.CFSGTypeASLTwoWeyl
