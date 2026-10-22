import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Torsion.Field

/-! The Jacobi calculation that makes a length-one root string have
inverse coefficients. Actual root-degree vanishing and Cartan weights
must be supplied by the original representation at application time. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGSlTwoUnitString
variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

theorem lowering_after_raising (E F H X : L)
    (hEF : ⁅E,F⁆=H) (hHX : ⁅H,X⁆= -X) (hFX : ⁅F,X⁆=0) :
    ⁅F,⁅E,X⁆⁆=X := by
  rw [leibniz_lie,←lie_skew F E,hEF,neg_lie,hHX,hFX,lie_zero,neg_neg,add_zero]

theorem inverse_root_string_coefficients (E F H X Y : L) (c d : K)
    (hEF : ⁅E,F⁆=H) (hHX : ⁅H,X⁆= -X) (hFX : ⁅F,X⁆=0)
    (hEX : ⁅E,X⁆=c • Y) (hFY : ⁅F,Y⁆=d • X) (hX : X≠0) : c*d=1 := by
  have hh := lowering_after_raising E F H X hEF hHX hFX
  rw [hEX,lie_smul,hFY,smul_smul] at hh
  have hz : (c*d-1) • X=0 := by rw [sub_smul,one_smul,hh,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hX)

end SymmetricSubgroupAsymptotics.CFSGSlTwoUnitString
