import SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
import Mathlib.Tactic.Group

/-! Exact scalar lifting of equality in the literal PSL2 quotient. The
central scalar has square one; projective equality is never replaced by
literal equality of its determinant-one matrix representatives. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
open Matrix CFSGTypeASLTwoWeyl CFSGTypeARootTorus
variable {F : Type*} [Field F]

theorem projection_eq_implies_scalar_mul (x y : SL2 (F:=F))
    (h : projection x=projection y) :
    ∃ r : F,r^2=1 ∧ x.val=Matrix.scalar (Fin 2) r*y.val := by
  have hc : x/y∈Subgroup.center (SL2 (F:=F)) := QuotientGroup.eq_iff_div_mem.mp h
  obtain ⟨r,hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r,by simpa only [Fintype.card_fin] using hr,?_⟩
  have hxy : x=(x/y)*y := (div_mul_cancel x y).symm
  have hm := congrArg (fun z : SL2 (F:=F) => z.val) hxy
  change x.val=(x/y).val*y.val at hm
  rwa [←he] at hm

theorem projectiveTorus_eq_one_of_square (c : Fˣ) (hc : (c : F)^2=1) :
    projectiveTorus c=1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  have hu : c*c=1 := Units.ext (by simpa only [Units.val_mul,Units.val_one,pow_two] using hc)
  have hi : c⁻¹=c := inv_eq_of_mul_eq_one_right hu
  have hival : (c : F)⁻¹=(c : F) := by
    simpa only [Units.val_inv_eq_inv_val] using congrArg (fun u : Fˣ => (u : F)) hi
  refine ⟨(c : F),by simpa only [Fintype.card_fin] using hc,?_⟩
  rw [torus_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply,hival]

end SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
