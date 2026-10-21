import SymmetricSubgroupAsymptotics.CFSGSuzukiBorelPSubgroups
import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusElements

/-! The actual opposite Suzuki unipotent has trivial intersection with
the actual Borel. Two original entries of its first row recover its
unipotent parameters; no whole-group order argument is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiOppositeIntersection
open CFSGSuzukiUnipotent CFSGSuzukiBorelPSubgroups

theorem opposite_entry01 (m : ℕ) (a b : CFSGSuzukiFieldParameters.Field m) :
    ((CFSGSuzukiTorus.weylElement m*unipotentElement m a b*
      (CFSGSuzukiTorus.weylElement m)⁻¹ : Ambient m) :
      CFSG.Models.SuzukiConstruction.Mat m) 0 1=a := by
  rw [CFSGSuzukiTorus.weylElement_inv]
  simp [Matrix.GeneralLinearGroup.coe_mul,unipotentElement_coe,
    CFSGSuzukiTorus.weylElement_coe,CFSG.Models.SuzukiConstruction.weyl,
    CFSG.Models.SuzukiConstruction.unipotent,Matrix.mul_apply,Fin.sum_univ_succ]

theorem opposite_entry02 (m : ℕ) (a b : CFSGSuzukiFieldParameters.Field m) :
    ((CFSGSuzukiTorus.weylElement m*unipotentElement m a b*
      (CFSGSuzukiTorus.weylElement m)⁻¹ : Ambient m) :
      CFSG.Models.SuzukiConstruction.Mat m) 0 2=
        a*CFSGSuzukiFieldParameters.theta m a+b := by
  rw [CFSGSuzukiTorus.weylElement_inv]
  simp [Matrix.GeneralLinearGroup.coe_mul,unipotentElement_coe,
    CFSGSuzukiTorus.weylElement_coe,CFSG.Models.SuzukiConstruction.weyl,
    CFSG.Models.SuzukiConstruction.unipotent,Matrix.mul_apply,Fin.sum_univ_succ]

theorem borel_inf_opposite_unipotent (m : ℕ) :
    borelEnvelope m ⊓ (unipotentSubgroup m).map
      (MulAut.conj (CFSGSuzukiTorus.weylElement m)).toMonoidHom=⊥ := by
  apply bot_unique
  rintro _ ⟨hg,u,hu,rfl⟩
  obtain ⟨a,b,rfl⟩ := hu
  have ha := borel_first_row m _ hg 1 (by decide)
  have hb := borel_first_row m _ hg 2 (by decide)
  change ((CFSGSuzukiTorus.weylElement m*unipotentElement m a b*
    (CFSGSuzukiTorus.weylElement m)⁻¹ : Ambient m) :
    CFSG.Models.SuzukiConstruction.Mat m) 0 1=0 at ha
  change ((CFSGSuzukiTorus.weylElement m*unipotentElement m a b*
    (CFSGSuzukiTorus.weylElement m)⁻¹ : Ambient m) :
    CFSG.Models.SuzukiConstruction.Mat m) 0 2=0 at hb
  rw [opposite_entry01] at ha
  rw [opposite_entry02,ha,zero_mul,zero_add] at hb
  change CFSGSuzukiTorus.weylElement m*unipotentElement m a b*
    (CFSGSuzukiTorus.weylElement m)⁻¹=1
  rw [ha,hb,unipotentElement_zero,mul_one,mul_inv_cancel]

theorem weyl_not_mem_borel (m : ℕ) : CFSGSuzukiTorus.weylElement m∉borelEnvelope m := by
  intro hw
  have he := borel_first_row m _ hw 3 (by decide)
  have hentry : (CFSGSuzukiTorus.weylElement m :
      CFSG.Models.SuzukiConstruction.Mat m) 0 3=1 := by
    simp [CFSGSuzukiTorus.weylElement_coe,CFSG.Models.SuzukiConstruction.weyl]
  rw [hentry] at he
  exact one_ne_zero he

end SymmetricSubgroupAsymptotics.CFSGSuzukiOppositeIntersection
