import SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
import Mathlib.LinearAlgebra.Dimension.Constructions
import Lean.Elab.Tactic.Omega

/-! A projective transvection in dimension at least three has a unique
actual determinant-one transvection representative. Two representatives
have a common nonzero fixed vector, so the possible central scalar is
one. Consequently its centre line and axis are well defined in the
original vector space, before any abstract-automorphism recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
open Module LinearMap Matrix

section JointKernel
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem exists_nonzero_joint_kernel (f g : Dual F V) (hd : 3≤Module.finrank F V) :
    ∃x : V,x≠0 ∧ f x=0 ∧ g x=0 := by
  by_contra hn
  have hk : ∀x : V,f x=0→g x=0→x=0 := by
    intro x hx hy
    by_contra hx0
    exact hn ⟨x,hx0,hx,hy⟩
  have hi : Function.Injective (f.prod g) := by
    intro x y he
    apply sub_eq_zero.mp
    apply hk (x-y)
    · rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.fst he)
    · rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.snd he)
  have hdim := LinearMap.finrank_le_finrank_of_injective (f:=f.prod g) hi
  simp only [Module.finrank_prod,Module.finrank_self] at hdim
  omega
end JointKernel

variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem projection_eq_implies_scalar_mul (x y : SL (F:=F) (n:=n))
    (h : projection x=projection y) :
    ∃r : F,r^(Fintype.card n)=1 ∧ x.val=Matrix.scalar n r*y.val := by
  have hc : x/y∈Subgroup.center (SL (F:=F) (n:=n)) := QuotientGroup.eq_iff_div_mem.mp h
  obtain ⟨r,hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r,hr,?_⟩
  have hxy : x=(x/y)*y := (div_mul_cancel x y).symm
  have hm := congrArg (fun z : SL (F:=F) (n:=n) => z.val) hxy
  change x.val=(x/y).val*y.val at hm
  rwa [←he] at hm

theorem scalar_toLin'_apply (r : F) (x : n→F) :
    Matrix.toLin' (Matrix.scalar n r) x=r • x := by
  rw [Matrix.toLin'_apply]
  change Matrix.diagonal (fun _ : n => r) *ᵥ x=r • x
  ext i
  simp only [Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul]

/-- No nontrivial central scalar can relate two original transvections
when the original vector space has dimension at least three. -/
theorem transvectionSL_eq_of_projective_eq (hn : 3≤Fintype.card n)
    {f g : Dual F (n→F)} {v w : n→F} (hf : f v=0) (hg : g w=0)
    (he : projection (transvectionSL hf)=projection (transvectionSL hg)) :
    transvectionSL hf=transvectionSL hg := by
  obtain ⟨x,hx,hfx,hgx⟩ := exists_nonzero_joint_kernel f g
    (by simpa only [Module.finrank_fintype_fun_eq_card] using hn)
  obtain ⟨r,_hr,hrfg⟩ := projection_eq_implies_scalar_mul _ _ he
  have hv : (transvectionSL hf).toLin' x=r • (transvectionSL hg).toLin' x := by
    change Matrix.toLin' (transvectionSL hf).val x=r • Matrix.toLin' (transvectionSL hg).val x
    rw [hrfg,Matrix.toLin'_mul_apply,scalar_toLin'_apply]
  have hr : r=1 := smul_left_injective F hx (by
    simpa only [transvectionSL_apply,hfx,hgx,zero_smul,add_zero,one_smul] using hv.symm)
  apply Subtype.ext
  rw [hrfg,hr,map_one,one_mul]

theorem transvection_linearMap_eq_of_projective_eq (hn : 3≤Fintype.card n)
    {f g : Dual F (n→F)} {v w : n→F} (hf : f v=0) (hg : g w=0)
    (he : projection (transvectionSL hf)=projection (transvectionSL hg)) :
    LinearMap.transvection f v=LinearMap.transvection g w := by
  have hm := congrArg (fun A : SL (F:=F) (n:=n) => Matrix.toLin' A.val)
    (transvectionSL_eq_of_projective_eq hn hf hg he)
  change Matrix.toLin' (LinearMap.toMatrix' (LinearMap.transvection f v))=
    Matrix.toLin' (LinearMap.toMatrix' (LinearMap.transvection g w)) at hm
  simpa only [Matrix.toLin'_toMatrix'] using hm

theorem centre_eq_of_projective_transvection_eq (hn : 3≤Fintype.card n)
    {f g : Dual F (n→F)} {v w : n→F} (hf : f v=0) (hg : g w=0)
    (hf0 : f≠0) (hg0 : g≠0)
    (he : projection (transvectionSL hf)=projection (transvectionSL hg)) :
    F ∙ v=F ∙ w :=
  CFSGTypeATransvectionGeometry.centre_eq_of_transvection_eq hf0 hg0
    (transvection_linearMap_eq_of_projective_eq hn hf hg he)

theorem axis_eq_of_projective_transvection_eq (hn : 3≤Fintype.card n)
    {f g : Dual F (n→F)} {v w : n→F} (hf : f v=0) (hg : g w=0)
    (hv : v≠0) (hw : w≠0)
    (he : projection (transvectionSL hf)=projection (transvectionSL hg)) :
    LinearMap.ker f=LinearMap.ker g :=
  CFSGTypeATransvectionGeometry.axis_eq_of_transvection_eq hv hw
    (transvection_linearMap_eq_of_projective_eq hn hf hg he)

end SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots
