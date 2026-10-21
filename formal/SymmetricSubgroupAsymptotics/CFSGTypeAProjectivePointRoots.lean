import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionGeometry
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! Actual point-root groups in the original SL/PSL central quotient.
The parameters are all original linear forms annihilating a fixed vector,
not abstract root-group labels. Their projective map is injective because
a central transvection fixing a nonzero vector must be the identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
open Module LinearMap Matrix
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

abbrev SL := Matrix.SpecialLinearGroup n F
abbrev PSL := Matrix.ProjectiveSpecialLinearGroup n F

def projection : SL (F:=F) (n:=n)→*PSL (F:=F) (n:=n) :=
  QuotientGroup.mk' (Subgroup.center (SL (F:=F) (n:=n)))

def transvectionSL {f : Dual F (n→F)} {v : n→F} (hfv : f v=0) : SL (F:=F) (n:=n) :=
  ⟨LinearMap.toMatrix' (LinearMap.transvection f v),by
    rw [LinearMap.det_toMatrix',LinearMap.transvection.det,hfv,add_zero]⟩

@[simp] theorem transvectionSL_apply {f : Dual F (n→F)} {v : n→F}
    (hfv : f v=0) (x : n→F) :
    (transvectionSL hfv).toLin' x=x+f x • v := by
  change Matrix.toLin' (LinearMap.toMatrix' (LinearMap.transvection f v)) x=_
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem transvectionSL_mul {f g : Dual F (n→F)} {v : n→F}
    (hf : f v=0) (hg : g v=0) :
    transvectionSL hf*transvectionSL hg=
      transvectionSL (show (f+g) v=0 by simp only [LinearMap.add_apply,hf,hg,add_zero]) := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  rw [map_mul]
  apply LinearEquiv.ext
  intro x
  change (transvectionSL hf).toLin' ((transvectionSL hg).toLin' x)=
    (transvectionSL (show (f+g) v=0 by simp only [LinearMap.add_apply,hf,hg,add_zero])).toLin' x
  simp only [transvectionSL_apply,map_add,map_smul,hf,zero_smul,
    add_zero,LinearMap.add_apply,add_smul]
  abel

theorem transvectionSL_zero (v : n→F) :
    transvectionSL (show (0 : Dual F (n→F)) v=0 from rfl)=1 := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  rw [map_one]
  apply LinearEquiv.ext
  intro x
  change (transvectionSL (show (0 : Dual F (n→F)) v=0 from rfl)).toLin' x=x
  simp only [transvectionSL_apply,LinearMap.zero_apply,zero_smul,add_zero]

/-- The original dual hyperplane of forms vanishing on v. -/
def pointForms (v : n→F) : Submodule F (Dual F (n→F)) where
  carrier := {f | f v=0}
  zero_mem' := rfl
  add_mem' := by
    intro f g hf hg
    change f v=0 at hf
    change g v=0 at hg
    change (f+g) v=0
    simp only [LinearMap.add_apply,hf,hg,add_zero]
  smul_mem' := by
    intro c f hf
    change f v=0 at hf
    change (c • f) v=0
    simp only [LinearMap.smul_apply,hf,smul_zero]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem pointForms_apply_eq_zero (v : n→F) (f : pointForms v) : f.val v=0 :=
  f.property

local instance pointRootParameterCommGroup (v : n→F) : CommGroup (Multiplicative (pointForms v)) :=
  inferInstance

def pointRootSLHom (v : n→F) : Multiplicative (pointForms v)→*SL (F:=F) (n:=n) where
  toFun f := transvectionSL (pointForms_apply_eq_zero v f.toAdd)
  map_one' := transvectionSL_zero v
  map_mul' f g := (transvectionSL_mul f.toAdd.property g.toAdd.property).symm

@[simp] theorem pointRootSLHom_apply (v : n→F) (f : Multiplicative (pointForms v)) (x : n→F) :
    (pointRootSLHom v f).toLin' x=x+(f.toAdd.val x) • v := transvectionSL_apply (pointForms_apply_eq_zero v f.toAdd) x

def pointRootHom (v : n→F) : Multiplicative (pointForms v)→*PSL (F:=F) (n:=n) :=
  (projection (F:=F) (n:=n)).comp (pointRootSLHom v)

/-- The centre of the original SL group has trivial intersection with
this point-root group, including in positive characteristic. -/
theorem pointRootSL_eq_one_of_mem_center {v : n→F} (hv : v≠0)
    (f : Multiplicative (pointForms v))
    (hf : pointRootSLHom v f∈Subgroup.center (SL (F:=F) (n:=n))) :
    pointRootSLHom v f=1 := by
  obtain ⟨r,_hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hf
  have hscalar : (pointRootSLHom v f).toLin' v=r • v := by
    change Matrix.toLin' (pointRootSLHom v f).val v=r • v
    rw [←he,Matrix.toLin'_apply]
    change Matrix.diagonal (fun _ : n => r) *ᵥ v=r • v
    ext i
    simp only [Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul]
  have hr : r=1 := smul_left_injective F hv (by
    simpa only [pointRootSLHom_apply,pointForms_apply_eq_zero,zero_smul,add_zero,one_smul]
      using hscalar.symm)
  apply Subtype.ext
  rw [←he,hr]
  exact map_one (Matrix.scalar n)

theorem pointRootHom_injective {v : n→F} (hv : v≠0) :
    Function.Injective (pointRootHom v) := by
  apply (MonoidHom.ker_eq_bot_iff (pointRootHom v)).mp
  apply bot_unique
  intro f hf
  have hc : pointRootSLHom v f∈Subgroup.center (SL (F:=F) (n:=n)) :=
    (QuotientGroup.eq_one_iff _).mp hf
  have he := pointRootSL_eq_one_of_mem_center hv f hc
  have hz : f.toAdd=0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun a : SL (F:=F) (n:=n) => a.toLin' x) he
    dsimp only at hx
    rw [map_one,pointRootSLHom_apply] at hx
    change x+f.toAdd.val x • v=x at hx
    have hh : f.toAdd.val x • v=0 := add_left_cancel (hx.trans (add_zero x).symm)
    exact (smul_eq_zero.mp hh).resolve_right hv
  apply (Subgroup.mem_bot).mpr
  exact congrArg Multiplicative.ofAdd hz

def pointRoot (v : n→F) : Subgroup (PSL (F:=F) (n:=n)) := (pointRootHom v).range

def pointRootEquiv {v : n→F} (hv : v≠0) :
    Multiplicative (pointForms v)≃*pointRoot v :=
  MonoidHom.ofInjective (pointRootHom_injective hv)

end SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
