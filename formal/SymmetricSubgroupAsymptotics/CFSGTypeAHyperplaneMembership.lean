import SymmetricSubgroupAsymptotics.CFSGTypeAHyperplaneRoots
import SymmetricSubgroupAsymptotics.CFSGTypeARootMembership

/-! Exact membership in original projective hyperplane-root groups.
Equal kernels of nonzero original forms give a proved nonzero scalar
relation, and the root vector is rescaled by that same scalar. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootMembership
open Matrix Module LinearMap Submodule CFSGTypeAProjectivePointRoots CFSGTypeAHyperplaneRoots

section Forms
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem exists_unit_smul_of_ker_eq {f g : Dual F V} (hf : f≠0) (hg : g≠0)
    (he : LinearMap.ker f=LinearMap.ker g) : ∃a : Fˣ,f=(a : F) • g := by
  obtain ⟨x,hx⟩ := LinearMap.surjective hg (1 : F)
  have hval : ∀y,f y=g y*f x := by
    intro y
    have hgy : y-g y • x∈LinearMap.ker g := by
      change g (y-g y • x)=0
      simp only [map_sub,map_smul,hx,smul_eq_mul,mul_one,sub_self]
    have hfy : y-g y • x∈LinearMap.ker f := he.ge hgy
    change f (y-g y • x)=0 at hfy
    apply sub_eq_zero.mp
    simpa only [map_sub,map_smul,smul_eq_mul] using hfy
  have ha : f x≠0 := by
    intro hz
    apply hf
    apply LinearMap.ext
    intro y
    simpa only [hz,mul_zero] using hval y
  refine ⟨Units.mk0 (f x) ha,?_⟩
  apply LinearMap.ext
  intro y
  simpa only [LinearMap.smul_apply,Units.val_mk0,smul_eq_mul,mul_comm] using hval y
end Forms

variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem hyperplaneRoot_mem_iff_axis (hn : 3≤Fintype.card n)
    {f g : Dual F (n→F)} {v : n→F} (hfv : f v=0)
    (hf : f≠0) (hg : g≠0) (hv : v≠0) :
    projection (transvectionSL hfv)∈hyperplaneRoot g ↔ LinearMap.ker f=LinearMap.ker g := by
  constructor
  · rintro ⟨w,hw⟩
    have hw0 : w.toAdd.val≠0 := by
      intro he
      have hzero : w.toAdd=0 := Subtype.ext he
      have hwone : w=1 := congrArg Multiplicative.ofAdd hzero
      rw [hwone,map_one] at hw
      exact projective_transvection_ne_one hfv hf hv hw.symm
    have he : projection (transvectionSL hfv)=projection
        (transvectionSL (show g w.toAdd.val=0 from w.toAdd.property)) := hw.symm
    exact axis_eq_of_projective_transvection_eq hn hfv w.toAdd.property hv hw0 he
  · intro he
    obtain ⟨a,ha⟩ := exists_unit_smul_of_ker_eq hf hg he
    have hgv : g v=0 := he.le (show v∈LinearMap.ker f from hfv)
    have hvec : g ((a : F) • v)=0 := by simp only [map_smul,hgv,smul_zero]
    let w : Multiplicative (LinearMap.ker g) := Multiplicative.ofAdd ⟨(a : F) • v,hvec⟩
    refine ⟨w,?_⟩
    change projection (transvectionSL hvec)=projection (transvectionSL hfv)
    apply congrArg projection
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro x
    rw [transvectionSL_apply,transvectionSL_apply,ha]
    simp only [LinearMap.smul_apply,smul_eq_mul,smul_smul,mul_comm]

end SymmetricSubgroupAsymptotics.CFSGTypeARootMembership
