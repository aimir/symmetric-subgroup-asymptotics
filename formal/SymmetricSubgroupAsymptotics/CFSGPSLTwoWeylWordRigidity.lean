import SymmetricSubgroupAsymptotics.CFSGPSLTwoProjectiveScalars

/-! The constant rank-one Weyl word kills the residual projective torus
parameter. Its matrix representatives are compared only up to the actual
square-one scalar supplied by the defining PSL2 quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
open Matrix CFSGTypeASLTwoWeyl CFSGTypeARootTorus CFSGSLTwoUpperRoots
variable {F : Type*} [Field F]

theorem projectiveWeyl_word : projectiveWeyl (F:=F)=projectiveUpper 1*
    (projectiveWeyl*projectiveUpper 1*projectiveWeyl⁻¹)*projectiveUpper 1 := by
  rw [projective_weyl_upper]
  change projection (weyl (F:=F))=projection (upper 1)*projection (lower (-1))*projection (upper 1)
  rw [←map_mul,←map_mul]
  rfl

theorem projective_weyl_torus_word_rigidity (c : Fˣ)
    (hword : projectiveWeyl*projectiveTorus c=projectiveUpper 1*
      ((projectiveWeyl*projectiveTorus c)*projectiveUpper 1*
        (projectiveWeyl*projectiveTorus c)⁻¹)*projectiveUpper 1) :
    projectiveTorus c=1 := by
  have hconj : (projectiveWeyl*projectiveTorus c)*projectiveUpper 1*
      (projectiveWeyl*projectiveTorus c)⁻¹=projection (lower (-(c : F)^2)) := by
    calc
      _=projectiveWeyl*(projectiveTorus c*projectiveUpper 1*(projectiveTorus c)⁻¹)*projectiveWeyl⁻¹ := by group
      _=projectiveWeyl*projectiveUpper ((c : F)^2)*projectiveWeyl⁻¹ := by
        rw [projective_torus_conjugation,mul_one]
      _=projection (lower (-(c : F)^2)) := projective_weyl_upper _
  rw [hconj] at hword
  have hxy : projection (weyl*torus (by decide : (0 : Fin 2)≠1) c)=
      projection (upper 1*lower (-(c : F)^2)*upper 1) := by
    simpa only [map_mul,projectiveWeyl,projectiveTorus,projectiveUpper] using hword
  obtain ⟨r,hr,he⟩ := projection_eq_implies_scalar_mul _ _ hxy
  have hrne : r≠0 := by intro hz;rw [hz,zero_pow (by decide : 2≠0)] at hr;exact zero_ne_one hr
  have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 0) he
  have hleft : (weyl*torus (by decide : (0 : Fin 2)≠1) c : SL2 (F:=F)).val 0 0=0 := by
    change ((weyl (F:=F)).val*(torus (by decide : (0 : Fin 2)≠1) c).val) 0 0=0
    rw [sl_weyl_coe,torus_coe]
    simp [Matrix.mul_diagonal]
  have hright : (upper 1*lower (-(c : F)^2)*upper 1 : SL2 (F:=F)).val 0 0=1-(c : F)^2 := by
    simp [upper,lower,CFSGTypeAElementaryMatrices.elementary,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.transvection,Matrix.single_apply,Matrix.one_apply] <;> ring
  change (weyl*torus (by decide : (0 : Fin 2)≠1) c : SL2 (F:=F)).val 0 0=
    (Matrix.scalar (Fin 2) r*(upper 1*lower (-(c : F)^2)*upper 1 : SL2 (F:=F)).val) 0 0 at hentry
  rw [hleft,Matrix.scalar_apply,Matrix.diagonal_mul,hright] at hentry
  have hs : 1-(c : F)^2=0 := (mul_eq_zero.mp hentry.symm).resolve_left hrne
  exact projectiveTorus_eq_one_of_square c (sub_eq_zero.mp hs).symm

end SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
